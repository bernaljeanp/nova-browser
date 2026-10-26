const { app, BaseWindow, BrowserWindow, WebContentsView, ipcMain, session, Menu, clipboard, shell, nativeImage } = require('electron');
const { spawn } = require('child_process');
const { ElectronBlocker } = require('@ghostery/adblocker-electron');
const { DatabaseSync } = require('node:sqlite');
const fs = require('fs/promises');
const path = require('path');

// One Nova at a time: links opened from other apps arrive as a new tab in the running window.
const PRIMARY = app.requestSingleInstanceLock();
if (!PRIMARY) app.quit();
const urlArg = argv => argv.slice(1).find(a => /^(https?|file):\/\//i.test(a));

// Prefer the dedicated GPU (RTX) on dual-GPU laptops; Chromium already does GPU raster + hardware video decode.
app.commandLine.appendSwitch('force_high_performance_gpu');
// Split each download across several connections; helps most with servers that cap speed per connection.
app.commandLine.appendSwitch('enable-features', 'ParallelDownloading');

const UI_H = 84; // tab strip (38) + toolbar (46)
const page = f => 'file://' + path.join(__dirname, f).replace(/\\/g, '/');
const HOME = page('home.html'), WRAPPED = page('wrapped.html');
const AI_W = 400; // side panel width
const SB_CATS = ['sponsor', 'selfpromo', 'interaction', 'intro', 'outro', 'music_offtopic'];
const SLEEP_MS = 5 * 60e3; // background tabs idle this long free their memory
const TRACKING = /^(utm_\w+|fbclid|gclid|dclid|msclkid|mc_eid|igshid|yclid|_hsenc|_hsmi|si)$/i;
const DEV_PORTS = [3000, 3001, 3002, 4000, 4200, 4321, 5000, 5173, 5174, 5500, 8000, 8080, 8081, 8888, 9000];

let win, ui, USER, active = null, split = null, overlay = false, blocked = 0, nextId = 1;
let history = [], servers = [], bookmarks = []; // bookmarks: [{ url, title, favicon }]
const HISTORY_MAX = 5000;
const saveJSON = (name, data) => fs.writeFile(path.join(USER, name), JSON.stringify(data)).catch(() => {});
// YouTube pack; persisted in settings.json
let settings = { ytQuality: true, ytMusic: false, ytNoShorts: true, ytFocus: false, ytDislikes: true, autoPip: true };
const YT_LABELS = { ytQuality: 'Calidad máxima automática', ytMusic: 'Modo música (solo audio)', ytNoShorts: 'Ocultar Shorts', ytFocus: 'Modo sin distracciones', ytDislikes: 'Mostrar «No me gusta»' };
const LABELS = { ...YT_LABELS, autoPip: 'Video flotante automático' };

// Nova Wrapped: per-month counters, persisted in stats.json as { "2026-10": {...} }.
let stats = {};
const monthKey = () => new Date().toISOString().slice(0, 7);
const month = () => (stats[monthKey()] ??= { blocked: 0, videos: 0, sponsorSec: 0, channels: {} });
// ponytail: YouTube ad time is an estimate (one ~15 s ad per watched video); SponsorBlock time is measured.
const AD_SEC_PER_VIDEO = 15;
function statsSummary() {
  const m = month();
  return {
    month: monthKey(), blocked: m.blocked, videos: m.videos, sponsorMin: Math.round(m.sponsorSec / 60),
    saved: Math.round(m.videos * AD_SEC_PER_VIDEO + m.sponsorSec),
    top: Object.entries(m.channels).sort((a, b) => b[1] - a[1]).slice(0, 3).map(([name, n]) => ({ name, n })),
  };
}
const seenVideo = new Map(); // webContents id -> last counted video id

let aiView = null, aiOpen = false, aiTab = null, aiIdle;
const isYouTube = u => { try { return /(^|\.)youtube\.com$/.test(new URL(u).hostname); } catch { return false; } };
const closed = []; // urls of closed tabs, for Ctrl+Shift+T
// id -> { view, shown, lastSeen, favicon, errors } while awake, { url, title, favicon } while sleeping
const tabs = new Map();

const isLocal = u => { try { return /^(localhost|127\.0\.0\.1|\[::1\]|.+\.localhost|.+\.test)$/.test(new URL(u).hostname); } catch { return false; } };

function clean(raw) {
  try {
    const u = new URL(raw);
    for (const k of [...u.searchParams.keys()]) if (TRACKING.test(k)) u.searchParams.delete(k);
    return u.toString();
  } catch { return raw; }
}

function toUrl(input) {
  const s = input.trim();
  if (/^(https?|file):\/\//i.test(s)) return clean(s);
  if (/^:\d+/.test(s)) return 'http://localhost' + s; // ":5173" -> dev server
  if (/^(localhost|127\.0\.0\.1)(:\d+)?(\/|$)/.test(s)) return 'http://' + s;
  if (/^[\w-]+(\.[\w-]+)+(:\d+)?(\/\S*)?$/.test(s)) return clean('https://' + s); // HTTPS first
  return 'https://www.google.com/search?q=' + encodeURIComponent(s);
}

const info = t => t.view
  ? { url: t.view.webContents.getURL(), title: t.view.webContents.getTitle(), favicon: t.favicon, loading: t.view.webContents.isLoading(), errors: t.errors.length + t.net.length,
      audible: t.view.webContents.isCurrentlyAudible(), muted: t.view.webContents.isAudioMuted() }
  : { url: t.url, title: t.title, favicon: t.favicon, loading: false, errors: 0, sleeping: true };

function state() {
  if (!ui) return;
  const list = [...tabs].map(([id, t]) => {
    const i = info(t);
    return { ...i, id, title: i.title || 'Nueva pestaña', url: i.url === HOME ? '' : i.url };
  });
  const nav = tabs.get(active)?.view?.webContents.navigationHistory;
  const cur = tabs.get(active), curUrl = cur ? info(cur).url : '';
  // Mini player: the most recent tab with media that is not on screen.
  const m = [...tabs].filter(([id, t]) => t.view && t.media && id !== active && id !== split).sort((a, b) => b[1].mediaAt - a[1].mediaAt)[0];
  const media = m && { id: m[0], title: m[1].view.webContents.getTitle(), playing: m[1].media === 'playing', yt: isYouTube(m[1].view.webContents.getURL()) };
  ui.webContents.send('state', { tabs: list, active, split, blocked, canBack: !!nav?.canGoBack(), canFwd: !!nav?.canGoForward(),
    youtube: isYouTube(curUrl), yt: settings, ytLabels: YT_LABELS, media, aiOpen,
    bookmarked: bookmarks.some(b => b.url === curUrl) });
  aiView?.webContents.send('ai-page', { url: curUrl === HOME ? '' : curUrl, title: cur ? info(cur).title : '', video: isYouTube(curUrl) && /[?&]v=/.test(curUrl) });
}

function layout() {
  const { width: full, height: H } = win.getContentBounds(), h = H - UI_H;
  ui.setBounds({ x: 0, y: 0, width: full, height: overlay ? H : UI_H });
  const W = aiOpen ? full - AI_W : full;
  if (aiOpen) aiView.setBounds({ x: W, y: UI_H, width: AI_W, height: h });
  const a = tabs.get(active)?.view, b = split != null && tabs.get(split)?.view;
  if (b) {
    const half = Math.floor(W / 2);
    a?.setBounds({ x: 0, y: UI_H, width: half - 1, height: h });
    b.setBounds({ x: half + 1, y: UI_H, width: W - half - 1, height: h });
  } else a?.setBounds({ x: 0, y: UI_H, width: W, height: h });
}

// Attach exactly the visible views (active, plus split pane), waking sleeping tabs as needed.
function render() {
  const want = [active, split].filter(id => id != null && tabs.has(id));
  for (const id of want) if (!tabs.get(id).view) wake(id, tabs.get(id).url);
  for (const [id, t] of tabs) if (t.shown && !want.includes(id)) {
    win.contentView.removeChildView(t.view); t.shown = false; t.lastSeen = Date.now();
  }
  for (const id of want) { const t = tabs.get(id); if (!t.shown) { win.contentView.addChildView(t.view); t.shown = true; } }
  if (aiView) aiOpen ? win.contentView.addChildView(aiView) : win.contentView.removeChildView(aiView);
  if (overlay) win.contentView.addChildView(ui); // keep the palette above the pages
  layout();
  state();
}

// YouTube pack. CSS is keyed off classes on <html> so toggles apply live without re-inserting styles.
const YT_CSS = `
html.nova-noshorts ytd-reel-shelf-renderer,
html.nova-noshorts ytd-rich-shelf-renderer[is-shorts],
html.nova-noshorts ytd-rich-section-renderer:has(ytd-rich-shelf-renderer[is-shorts]),
html.nova-noshorts grid-shelf-view-model,
html.nova-noshorts ytd-rich-item-renderer:has(a[href^="/shorts/"]),
html.nova-noshorts ytd-video-renderer:has(a[href^="/shorts/"]),
html.nova-noshorts ytd-guide-entry-renderer:has(a[title="Shorts"]),
html.nova-noshorts ytd-mini-guide-entry-renderer[aria-label="Shorts"],
html.nova-noshorts yt-tab-shape[tab-title="Shorts"],
html.nova-focus ytd-watch-flexy #secondary,
html.nova-focus ytd-watch-flexy #comments,
html.nova-focus ytd-merch-shelf-renderer,
html.nova-focus .ytp-endscreen-content,
html.nova-focus .ytp-ce-element,
html.nova-focus .ytp-autonav-endscreen-countdown-overlay { display: none !important; }
html.nova-music #movie_player video { opacity: 0 !important; }
dislike-button-view-model button:has(.nova-dl) { width: auto !important; padding: 0 14px 0 10px !important; gap: 6px; }
.nova-dl { font: 500 14px Roboto, Arial, sans-serif; }`;

// Runs in the page. Idempotent: installs once, then main only updates cfg/dislikes and calls apply().
const YT_SCRIPT = `(() => {
  if (window.__novaYT) return;
  const S = window.__novaYT = { cfg: {}, dislikes: null };
  const player = () => document.getElementById('movie_player');
  const vid = () => new URLSearchParams(location.search).get('v');
  S.quality = () => {
    const p = player();
    if (!p || !p.getAvailableQualityLevels) return false;
    const lv = p.getAvailableQualityLevels().filter(q => q !== 'auto');
    if (!lv.length) return false;
    if (S.cfg.ytMusic || S.cfg.ytQuality) {
      const q = S.cfg.ytMusic ? lv[lv.length - 1] : lv[0]; // music: lowest video = least data and decode work
      p.setPlaybackQualityRange && p.setPlaybackQualityRange(q, q);
      p.setPlaybackQuality && p.setPlaybackQuality(q);
    }
    return true;
  };
  S.dislike = () => {
    const b = document.querySelector('ytd-watch-metadata dislike-button-view-model button');
    if (!b) return !vid();
    let s = b.querySelector('.nova-dl');
    if (!S.cfg.ytDislikes || S.dislikes == null) { if (s) s.remove(); return true; }
    if (!s) { s = document.createElement('span'); s.className = 'nova-dl'; b.append(s); }
    s.textContent = new Intl.NumberFormat('es', { notation: 'compact' }).format(S.dislikes);
    return true;
  };
  // Reports the channel once per video for Nova Wrapped (main listens on the console).
  S.channel = () => {
    const id = vid();
    if (!id || S.reported === id) return true;
    const a = document.querySelector('ytd-watch-metadata ytd-channel-name a');
    if (!a || !a.textContent.trim()) return false;
    S.reported = id;
    console.debug('__nova:channel:' + a.textContent.trim());
    return true;
  };
  S.apply = () => {
    const h = document.documentElement.classList;
    h.toggle('nova-noshorts', !!S.cfg.ytNoShorts);
    h.toggle('nova-focus', !!S.cfg.ytFocus);
    h.toggle('nova-music', !!S.cfg.ytMusic);
    const p = player(), id = vid();
    if (p) p.style.background = S.cfg.ytMusic && id ? '#000 url(https://i.ytimg.com/vi/' + id + '/hqdefault.jpg) center/contain no-repeat' : '';
    // the player and the like bar render late; retry for ~10 s
    let n = 0;
    clearInterval(S.timer);
    S.timer = setInterval(() => { const a = S.quality(), b = S.dislike(), c = S.channel(); if ((a && b && c) || ++n > 20) clearInterval(S.timer); }, 500);
  };
  document.addEventListener('yt-navigate-finish', () => S.apply());
})()`;

async function youtube(wc, url) {
  if (!isYouTube(url) || wc.isDestroyed()) return;
  const u = new URL(url);
  if (settings.ytNoShorts && u.pathname.startsWith('/shorts/')) return wc.loadURL('https://www.youtube.com/watch?v=' + u.pathname.split('/')[2]);
  await wc.executeJavaScript(`${YT_SCRIPT}; window.__novaYT.dislikes = null; window.__novaYT.cfg = ${JSON.stringify(settings)}; window.__novaYT.apply();`).catch(() => {});
  const id = u.searchParams.get('v');
  if (!id) return;
  if (seenVideo.get(wc.id) !== id) { seenVideo.set(wc.id, id); month().videos++; }
  sponsorBlock(wc, id);
  if (!settings.ytDislikes) return;
  try {
    const r = await fetch(`https://returnyoutubedislikeapi.com/votes?videoId=${encodeURIComponent(id)}`, { signal: AbortSignal.timeout(5000) });
    const { dislikes } = await r.json();
    if (!wc.isDestroyed() && new URL(wc.getURL()).searchParams.get('v') === id && Number.isFinite(dislikes))
      wc.executeJavaScript(`window.__novaYT.dislikes = ${dislikes}; window.__novaYT.apply();`).catch(() => {});
  } catch {} // API down or offline: no count shown
}

// Nova IA context. Captions come from the player's own track list (same origin, so YouTube's CSP allows it),
// merged into ~30 s chunks so a long video fits the model's context.
const TRANSCRIPT = `(async () => {
  const p = document.getElementById('movie_player');
  const pr = (p && p.getPlayerResponse && p.getPlayerResponse()) || window.ytInitialPlayerResponse || {};
  const vd = pr.videoDetails || {};
  const tracks = (pr.captions && pr.captions.playerCaptionsTracklistRenderer && pr.captions.playerCaptionsTracklistRenderer.captionTracks) || [];
  const track = tracks.find(t => /^es/.test(t.languageCode) && t.kind !== 'asr') || tracks.find(t => /^es/.test(t.languageCode)) || tracks.find(t => t.kind !== 'asr') || tracks[0];
  const ts = s => { s = Math.floor(s); const h = Math.floor(s / 3600), m = Math.floor(s / 60) % 60, x = String(s % 60).padStart(2, '0'); return h ? h + ':' + String(m).padStart(2, '0') + ':' + x : m + ':' + x; };
  const chunks = [];
  if (track) try {
    const j = await (await fetch(track.baseUrl + '&fmt=json3')).json();
    let start = -1, text = '';
    for (const ev of j.events || []) {
      const t = (ev.segs || []).map(s => s.utf8).join('').replace(/\\s+/g, ' ').trim();
      if (!t) continue;
      const sec = (ev.tStartMs || 0) / 1000;
      if (start < 0) start = sec;
      text += ' ' + t;
      if (sec - start >= 30) { chunks.push('[' + ts(start) + ']' + text); start = -1; text = ''; }
    }
    if (text) chunks.push('[' + ts(start) + ']' + text);
  } catch (e) {}
  return { title: vd.title || document.title, channel: vd.author || '', description: (vd.shortDescription || '').slice(0, 3000), transcript: chunks.join('\\n') };
})()`;
const PAGE_TEXT = `(() => {
  const root = document.querySelector('article, main, [role=main]') || document.body;
  return { title: document.title, text: (root.innerText || '').replace(/\\n{3,}/g, '\\n\\n').slice(0, 40000) };
})()`;

// Uses an installed Ollama when there is one (faster, bigger models); otherwise the panel runs its built-in WebGPU model.
// Returns model names, or [] when Ollama is absent or has no models.
async function ensureOllama() {
  const tags = async () => {
    try { const r = await fetch('http://127.0.0.1:11434/api/tags', { signal: AbortSignal.timeout(1200) }); return r.ok ? (await r.json()).models.map(m => m.name) : null; }
    catch { return null; }
  };
  let m = await tags();
  if (m) return m;
  const exe = path.join(process.env.LOCALAPPDATA || '', 'Programs', 'Ollama', 'ollama.exe');
  if (!require('fs').existsSync(exe)) return [];
  // Starting the server is only worth it when some model is already downloaded.
  if (!require('fs').existsSync(path.join(require('os').homedir(), '.ollama', 'models', 'manifests'))) return [];
  spawn(exe, ['serve'], { detached: true, stdio: 'ignore', windowsHide: true }).unref();
  for (let i = 0; i < 20 && !m; i++) { await new Promise(r => setTimeout(r, 500)); m = await tags(); }
  return m || [];
}

// Push changed settings into every open YouTube tab.
function applyYouTubeAll() {
  for (const t of tabs.values()) if (t.view && isYouTube(t.view.webContents.getURL())) youtube(t.view.webContents, t.view.webContents.getURL());
}

// SponsorBlock: segments are fetched here (YouTube's CSP blocks it from the page), then a skipper is injected.
async function sponsorBlock(wc, id) {
  let segs = [];
  try {
    const r = await fetch(`https://sponsor.ajay.app/api/skipSegments?videoID=${encodeURIComponent(id)}&categories=${encodeURIComponent(JSON.stringify(SB_CATS))}`);
    if (r.ok) segs = (await r.json()).map(s => s.segment);
  } catch {} // 404 = no segments, offline = skip nothing
  if (wc.isDestroyed()) return;
  wc.executeJavaScript(`(() => {
    window.__novaSegs = ${JSON.stringify(segs)};
    if (window.__novaSB) return;
    window.__novaSB = true;
    document.addEventListener('timeupdate', e => {
      const v = e.target;
      if (!(v instanceof HTMLVideoElement)) return;
      for (const [a, b] of window.__novaSegs) if (v.currentTime >= a && v.currentTime < b - 0.3) {
        console.debug('__nova:skip:' + (b - v.currentTime)); // seconds saved, for Nova Wrapped
        v.currentTime = b;
      }
    }, true);
  })()`).catch(() => {});
}

// Local dev servers: a port counts when it answers HTTP; the <title> names it.
async function scanServers() {
  const found = await Promise.all(DEV_PORTS.map(async port => {
    try {
      const r = await fetch(`http://localhost:${port}/`, { signal: AbortSignal.timeout(700) });
      const title = ((await r.text()).match(/<title[^>]*>([^<]*)<\/title>/i)?.[1] || '').trim();
      return { port, url: `http://localhost:${port}/`, title };
    } catch { return null; }
  }));
  servers = found.filter(Boolean);
}

function remember(url, title) {
  if (!/^https?:/.test(url)) return;
  history = [{ url, title: title || url, t: Date.now() }, ...history.filter(h => h.url !== url)].slice(0, HISTORY_MAX);
}

// Shown on the new-tab page until the user saves favorites of their own.
const DEFAULT_SITES = [
  { url: 'https://www.youtube.com/', title: 'YouTube' }, { url: 'https://mail.google.com/', title: 'Gmail' },
  { url: 'https://web.whatsapp.com/', title: 'WhatsApp' }, { url: 'https://github.com/', title: 'GitHub' },
  { url: 'https://claude.ai/', title: 'Claude' }, { url: 'https://www.netflix.com/', title: 'Netflix' },
];

// Site logos for the new-tab tiles: fetched once from DuckDuckGo's icon service (no tracking, unlike Google's)
// and kept as data URLs in icons.json, so the page works offline and never re-asks. '' = no icon available.
let icons = {};
const siteHost = u => { try { return new URL(u).hostname.replace(/^www\./, ''); } catch { return ''; } };
async function fetchIcons(list) {
  const missing = [...new Set(list.map(b => siteHost(b.url)))].filter(h => h && !(h in icons)).slice(0, 30);
  if (!missing.length) return false;
  await Promise.all(missing.map(async h => {
    icons[h] = '';
    // Subdomains often have no icon of their own (web.whatsapp.com), so fall back to the parent domain.
    for (const d of new Set([h, h.split('.').slice(-2).join('.')])) {
      try {
        const r = await fetch(`https://icons.duckduckgo.com/ip3/${encodeURIComponent(d)}.ico`, { signal: AbortSignal.timeout(5000) });
        const buf = Buffer.from(await r.arrayBuffer());
        if (r.ok && buf.length > 64) { icons[h] = `data:${r.headers.get('content-type') || 'image/x-icon'};base64,${buf.toString('base64')}`; break; }
      } catch { break; } // offline: letter tile, retried next launch
    }
  }));
  saveJSON('icons.json', icons);
  return true;
}

// Home and Wrapped are plain files without IPC: main pushes their data in.
function refreshHomes() {
  const mine = bookmarks.length > 0, sites = mine ? bookmarks.slice(0, 24) : DEFAULT_SITES;
  const homeIcons = Object.fromEntries(sites.map(b => [siteHost(b.url), icons[siteHost(b.url)] || '']));
  for (const t of tabs.values()) {
    const w = t.view?.webContents, u = w?.getURL();
    if (u === HOME) w.executeJavaScript(`window.renderHome?.(${JSON.stringify({ sites, mine, icons: homeIcons, stats: statsSummary() })})`).catch(() => {});
    if (u === WRAPPED) w.executeJavaScript(`window.renderWrapped?.(${JSON.stringify(statsSummary())})`).catch(() => {});
  }
  fetchIcons(sites).then(got => got && refreshHomes());
}

// Renders the Wrapped card at Instagram portrait size (1080x1350) in a hidden window.
// The window is reused: recreating hidden windows back-to-back can abort their first load.
let shareWin, shareIdle;
async function shareWrapped() {
  clearTimeout(shareIdle);
  // Offscreen so it keeps painting while hidden (a plain hidden window never produces the frame to capture).
  shareWin ??= new BrowserWindow({ width: 600, height: 600, show: false, webPreferences: { sandbox: true, offscreen: true } });
  await shareWin.loadURL(WRAPPED + '#card');
  await shareWin.webContents.executeJavaScript(`renderWrapped(${JSON.stringify(statsSummary())})`);
  // Windows clamps any window (even offscreen) to the monitor size, which crops a 1350 px card on a laptop.
  // Emulating the viewport through DevTools renders the exact size whatever the screen.
  const dbg = shareWin.webContents.debugger;
  if (!dbg.isAttached()) dbg.attach('1.3');
  await dbg.sendCommand('Emulation.setDeviceMetricsOverride', { width: 1080, height: 1350, deviceScaleFactor: 1, mobile: false });
  await new Promise(r => setTimeout(r, 350)); // fonts + layout
  const { data } = await dbg.sendCommand('Page.captureScreenshot', { format: 'png', captureBeyondViewport: true, clip: { x: 0, y: 0, width: 1080, height: 1350, scale: 1 } });
  const img = nativeImage.createFromBuffer(Buffer.from(data, 'base64'));
  shareIdle = setTimeout(() => { shareWin?.destroy(); shareWin = null; }, 60e3);
  const dir = path.join(app.getPath('pictures'), 'Nova');
  await fs.mkdir(dir, { recursive: true });
  const file = path.join(dir, `nova-wrapped-${monthKey()}.png`);
  await fs.writeFile(file, img.toPNG());
  clipboard.writeImage(img);
  shell.showItemInFolder(file);
  toast('Tu Nova Wrapped está copiado: pégalo en Instagram, TikTok o WhatsApp');
}

function setBookmarks(list) {
  bookmarks = list;
  saveJSON('bookmarks.json', bookmarks);
  refreshHomes();
  state();
}

// Chromium-family browsers share one profile format: Bookmarks is JSON, History is SQLite.
const BROWSERS = { Chrome: 'Google\\Chrome', Edge: 'Microsoft\\Edge', Brave: 'BraveSoftware\\Brave-Browser' };

async function importFrom(name) {
  const root = path.join(process.env.LOCALAPPDATA || '', BROWSERS[name] || '-', 'User Data');
  const dirs = (await fs.readdir(root).catch(() => [])).filter(d => d === 'Default' || /^Profile \d+$/.test(d)).map(d => path.join(root, d));
  if (!dirs.length) return toast(`No encontré ${name} en este equipo`);
  const marks = [...bookmarks], seenB = new Set(marks.map(b => b.url)), seenH = new Set(history.map(h => h.url));
  let nb = 0, nh = 0, locked = false;
  for (const dir of dirs) {
    try {
      const walk = n => {
        if (n.type === 'url' && /^https?:/.test(n.url) && !seenB.has(n.url)) { marks.push({ url: n.url, title: n.name || n.url, favicon: '' }); seenB.add(n.url); nb++; }
        for (const c of n.children || []) walk(c);
      };
      for (const r of Object.values(JSON.parse(await fs.readFile(path.join(dir, 'Bookmarks'), 'utf8')).roots)) if (r && typeof r === 'object') walk(r);
    } catch {} // profile without bookmarks
    // History is locked while that browser runs, so read a copy. Times are µs since 1601; convert in SQL to stay in safe-integer range.
    const tmp = path.join(app.getPath('temp'), `nova-import-${process.pid}-${nb}-${nh}.db`);
    try {
      await fs.copyFile(path.join(dir, 'History'), tmp);
      const db = new DatabaseSync(tmp, { readOnly: true });
      const rows = db.prepare(`SELECT url, title, CAST(last_visit_time / 1000 - 11644473600000 AS INTEGER) AS t
        FROM urls WHERE hidden = 0 AND url LIKE 'http%' ORDER BY last_visit_time DESC LIMIT ${HISTORY_MAX}`).all();
      db.close();
      for (const r of rows) if (!seenH.has(r.url)) { history.push({ url: r.url, title: r.title || r.url, t: r.t }); seenH.add(r.url); nh++; }
    } catch (e) { if (/EBUSY|EPERM|locked/i.test(e.code + e.message)) locked = true; }
    finally { await fs.rm(tmp, { force: true }).catch(() => {}); }
  }
  history = history.sort((a, b) => b.t - a.t).slice(0, HISTORY_MAX);
  saveJSON('history.json', history);
  setBookmarks(marks);
  toast(`${name}: ${nb} favoritos y ${nh} páginas importadas${locked ? ` · cierra ${name} para traer el historial` : ''}`);
}

// Links from the new-tab page to https://nova.invalid/... are Nova commands. The .invalid TLD is reserved,
// and will-navigate cancels them before any request leaves the machine.
const NOVA_CMD = 'https://nova.invalid/';
function novaLink(raw) {
  const u = new URL(raw), [verb, arg] = u.pathname.slice(1).split('/');
  if (verb === 'import') importFrom(arg);
  if (verb === 'wrapped') newTab(WRAPPED);
  if (verb === 'share') shareWrapped().catch(() => toast('No se pudo crear la imagen'));
  if (verb === 'unbookmark') setBookmarks(bookmarks.filter(b => b.url !== u.searchParams.get('url')));
}

function toast(msg) { ui.webContents.send('toast', msg); }

async function saveShot(image, name) {
  const dir = path.join(USER, 'capturas');
  await fs.mkdir(dir, { recursive: true });
  const file = path.join(dir, `${name}-${Date.now()}.png`);
  await fs.writeFile(file, image.toPNG());
  return file;
}

// "Señalar a la IA": runs in the page, highlights the hovered element and resolves with its context on click.
const PICKER = `new Promise(resolve => {
  const ui = document.createElement('div'), tag = document.createElement('div');
  ui.style.cssText = 'position:fixed;pointer-events:none;z-index:2147483647;border:2px solid #2fd4c7;background:#2fd4c722;border-radius:3px';
  tag.style.cssText = 'position:fixed;pointer-events:none;z-index:2147483647;background:#0a0b10;color:#e8e9f3;font:12px ui-monospace,Consolas,monospace;padding:4px 7px;border-radius:5px;white-space:nowrap';
  document.documentElement.append(ui, tag);
  const sel = el => {
    const parts = [];
    for (let n = el; n && n.nodeType === 1 && parts.length < 5; n = n.parentElement) {
      if (n.id) { parts.unshift('#' + CSS.escape(n.id)); break; }
      let p = n.localName + [...n.classList].slice(0, 2).map(c => '.' + CSS.escape(c)).join('');
      const sib = n.parentElement ? [...n.parentElement.children].filter(c => c.localName === n.localName) : [];
      if (sib.length > 1) p += ':nth-of-type(' + (sib.indexOf(n) + 1) + ')';
      parts.unshift(p);
    }
    return parts.join(' > ');
  };
  const component = el => {
    const fk = Object.keys(el).find(k => k.startsWith('__reactFiber$'));
    for (let f = fk && el[fk]; f; f = f.return) {
      const t = f.type, name = t && typeof t !== 'string' && (t.displayName || t.name);
      if (name) { const s = f._debugSource; return { name: '<' + name + '>', src: s ? s.fileName + ':' + s.lineNumber : '' }; }
    }
    for (let n = el; n; n = n.parentElement) {
      const v = n.__vueParentComponent;
      if (v) return { name: '<' + (v.type.name || v.type.__name || 'Anonymous') + '>', src: v.type.__file || '' };
    }
    return { name: '', src: '' };
  };
  let cur;
  const stop = e => { e.preventDefault(); e.stopPropagation(); };
  const move = e => {
    cur = e.target; const r = cur.getBoundingClientRect();
    Object.assign(ui.style, { left: r.left + 'px', top: r.top + 'px', width: r.width + 'px', height: r.height + 'px' });
    tag.textContent = (component(cur).name || cur.localName) + '  ' + Math.round(r.width) + '×' + Math.round(r.height);
    tag.style.left = Math.max(4, r.left) + 'px'; tag.style.top = (r.top > 30 ? r.top - 28 : r.bottom + 6) + 'px';
  };
  const end = val => {
    for (const [t, f] of evs) removeEventListener(t, f, true);
    ui.remove(); tag.remove(); resolve(val);
  };
  const click = e => {
    stop(e);
    if (!cur) return end(null);
    const r = cur.getBoundingClientRect(), cs = getComputedStyle(cur);
    const props = ['display', 'position', 'width', 'height', 'margin', 'padding', 'color', 'background-color', 'font-size', 'font-weight', 'font-family', 'border', 'border-radius', 'gap', 'flex-direction', 'justify-content', 'align-items', 'grid-template-columns', 'z-index', 'opacity'];
    end({
      url: location.href, selector: sel(cur), comp: component(cur),
      text: (cur.innerText || '').trim().slice(0, 200),
      html: cur.outerHTML.length > 1500 ? cur.outerHTML.slice(0, 1500) + '\\n<!-- … recortado -->' : cur.outerHTML,
      styles: props.map(p => [p, cs.getPropertyValue(p)]).filter(([p, v]) => v && !['none', 'normal', 'auto', '0px', 'rgba(0, 0, 0, 0)', 'static', '1', 'row', 'stretch'].includes(v) && !/^0px none/.test(v)).map(([p, v]) => p + ': ' + v).join('; '),
      rect: { x: r.left, y: r.top, width: r.width, height: r.height }, viewport: innerWidth + '×' + innerHeight,
    });
  };
  const key = e => { if (e.key === 'Escape') { stop(e); end(null); } };
  const evs = [['mousemove', move], ['click', click], ['keydown', key], ['mousedown', stop], ['mouseup', stop], ['pointerdown', stop], ['pointerup', stop]];
  for (const [t, f] of evs) addEventListener(t, f, true);
})`;

function contextMenu(wc, p) {
  const items = [];
  if (p.linkURL) items.push(
    { label: 'Abrir enlace en nueva pestaña', click: () => newTab(clean(p.linkURL), false) },
    { label: 'Abrir enlace en vista dividida', click: () => { const id = newTab(clean(p.linkURL), false); split = id; render(); } },
    { label: 'Copiar enlace', click: () => clipboard.writeText(clean(p.linkURL)) }, { type: 'separator' });
  if (p.mediaType === 'image') items.push(
    { label: 'Copiar imagen', click: () => wc.copyImageAt(p.x, p.y) },
    { label: 'Abrir imagen en nueva pestaña', click: () => newTab(p.srcURL, false) }, { type: 'separator' });
  if (p.isEditable) items.push({ role: 'undo', label: 'Deshacer' }, { role: 'cut', label: 'Cortar' }, { role: 'copy', label: 'Copiar' },
    { role: 'paste', label: 'Pegar' }, { role: 'selectAll', label: 'Seleccionar todo' }, { type: 'separator' });
  else if (p.selectionText.trim()) items.push({ role: 'copy', label: 'Copiar' },
    { label: `Buscar «${p.selectionText.trim().slice(0, 30)}» en Google`, click: () => newTab(toUrl(p.selectionText)) }, { type: 'separator' });
  if (!p.linkURL && !p.isEditable && !p.selectionText.trim()) items.push(
    { label: 'Atrás', enabled: wc.navigationHistory.canGoBack(), click: () => wc.navigationHistory.goBack() },
    { label: 'Adelante', enabled: wc.navigationHistory.canGoForward(), click: () => wc.navigationHistory.goForward() },
    { label: 'Recargar', click: () => wc.reload() }, { type: 'separator' },
    { label: 'Señalar elemento a la IA', click: cmd.pick },
    { label: 'Copiar paquete de depuración', click: cmd.copyErrors },
    { label: 'Captura al portapapeles', click: cmd.shot }, { type: 'separator' });
  items.push({ label: 'Inspeccionar', click: () => wc.inspectElement(p.x, p.y) });
  Menu.buildFromTemplate(items).popup();
}

// Shortcuts must work whichever view has focus, so every webContents routes keys here.
function keys(target) {
  target.on('before-input-event', (e, i) => {
    if (i.type !== 'keyDown') return;
    const k = i.key.toLowerCase(), c = i.control || i.meta, s = i.shift;
    const run = c && !s && k === 't' ? cmd.newTab
      : c && s && k === 't' ? cmd.reopen
      : c && k === 'w' ? () => cmd.close()
      : c && k === 'k' ? cmd.palette
      : c && k === 'l' ? () => { ui.webContents.focus(); ui.webContents.send('focus-url'); }
      : c && k === 'f' ? () => { ui.webContents.focus(); ui.webContents.send('find'); }
      : c && s && k === 'r' ? cmd.hardReload
      : (c && k === 'r') || k === 'f5' ? cmd.reload
      : i.alt && k === 'arrowleft' ? cmd.back
      : i.alt && k === 'arrowright' ? cmd.fwd
      : c && k === 'tab' ? () => { const ids = [...tabs.keys()], n = ids.length;
          select(ids[(ids.indexOf(active) + (s ? n - 1 : 1)) % n]); }
      : c && /^[1-9]$/.test(k) ? () => { const ids = [...tabs.keys()]; select(k === '9' ? ids.at(-1) : ids[+k - 1] ?? active); }
      : c && (k === '=' || k === '+') ? () => cmd.zoom(1)
      : c && k === '-' ? () => cmd.zoom(-1)
      : c && k === '0' ? () => cmd.zoom(0)
      : c && k === '\\' ? cmd.split
      : c && !s && k === 'd' ? cmd.bookmark
      : c && !s && k === 'j' ? cmd.ai
      : c && s && k === 'm' ? () => cmd.mute()
      : c && s && k === 's' ? cmd.shot
      : c && s && k === 'e' ? cmd.copyErrors
      : c && s && k === 'x' ? cmd.pick
      : c && s && k === 'p' ? cmd.pip
      : k === 'f12' || (c && s && k === 'i') ? cmd.devtools
      : null;
    if (run) { e.preventDefault(); run(); }
  });
}

function wake(id, url) {
  const t = { view: new WebContentsView({ webPreferences: { sandbox: true, contextIsolation: true } }),
    shown: false, favicon: tabs.get(id)?.favicon || '', lastSeen: Date.now(), errors: [], net: [] };
  const wc = t.view.webContents;
  tabs.set(id, t);
  keys(wc);
  wc.setWindowOpenHandler(({ url }) => { newTab(clean(url)); return { action: 'deny' }; });
  wc.on('will-navigate', (e, u) => {
    // Only Nova's own pages may send commands.
    if (u.startsWith(NOVA_CMD)) { e.preventDefault(); if ([HOME, WRAPPED].includes(wc.getURL())) novaLink(u); return; }
    const c = clean(u); if (c !== u) { e.preventDefault(); wc.loadURL(c); }
  });
  wc.on('did-finish-load', () => { if ([HOME, WRAPPED].includes(wc.getURL())) refreshHomes(); });
  wc.on('audio-state-changed', state);
  wc.on('media-started-playing', () => { t.media = 'playing'; t.mediaAt = Date.now(); state(); });
  wc.on('media-paused', () => { if (t.media) { t.media = 'paused'; state(); } });
  wc.on('page-favicon-updated', (_e, f) => { t.favicon = f[0]; state(); });
  wc.on('did-navigate', (_e, u) => { t.favicon = ''; t.errors = []; t.net = []; t.media = null; remember(u, ''); state(); });
  wc.on('did-navigate-in-page', (_e, u, main) => { if (!main) return; remember(u, wc.getTitle()); youtube(wc, u); state(); });
  wc.on('dom-ready', () => { const u = wc.getURL(); if (isYouTube(u)) { wc.insertCSS(YT_CSS); youtube(wc, u); } });
  wc.on('page-title-updated', (_e, title) => { const h = history.find(h => h.url === wc.getURL()); if (h) h.title = title; state(); });
  wc.on('console-message', e => {
    // Nova's own YouTube scripts report through the console; only trusted from youtube.com and clamped.
    const msg = /^__nova:(skip|channel):(.+)$/.exec(e.message);
    if (msg && isYouTube(wc.getURL())) {
      const mo = month();
      if (msg[1] === 'skip') mo.sponsorSec += Math.min(600, Math.max(0, +msg[2] || 0));
      else if (Object.keys(mo.channels).length < 500) { const ch = msg[2].slice(0, 80); mo.channels[ch] = (mo.channels[ch] || 0) + 1; }
      return;
    }
    if (e.level !== 'error' || t.errors.length >= 100) return;
    t.errors.push(`${e.message}${e.sourceId ? `\n   at ${e.sourceId}:${e.lineNumber}` : ''}`);
    state();
  });
  wc.on('did-fail-load', (_e, code, desc, u, main) => { if (main && code !== -3) { t.errors.push(`Carga fallida (${code} ${desc}): ${u}`); state(); } });
  wc.on('render-process-gone', (_e, d) => { t.errors.push(`El proceso de la página terminó: ${d.reason}`); state(); });
  wc.on('context-menu', (_e, p) => contextMenu(wc, p));
  wc.on('found-in-page', (_e, r) => ui.webContents.send('found', r));
  for (const ev of ['did-start-loading', 'did-stop-loading']) wc.on(ev, state);
  wc.loadURL(url);
}

function newTab(url = HOME, focus = true) {
  const id = nextId++;
  tabs.set(id, { url, title: '', favicon: '' });
  if (focus) select(id); else { wake(id, url); state(); }
  return id;
}

const PIP_ON = `(() => { const v = [...document.querySelectorAll('video')].find(v => !v.paused && v.readyState > 2);
  if (v && !document.pictureInPictureElement && !v.disablePictureInPicture) return v.requestPictureInPicture().catch(() => {}); })()`;
const PIP_OFF = `document.pictureInPictureElement && document.exitPictureInPicture().catch(() => {})`;

function select(id) {
  if (!tabs.has(id) || id === active) return render();
  const prev = tabs.get(active);
  // Auto picture-in-picture: a video playing in the tab you leave keeps playing in a floating window.
  // Not when it stays on screen (split view) or in music mode, where the video is hidden on purpose.
  if (settings.autoPip && prev?.view && prev.media === 'playing' && id !== split
      && !(settings.ytMusic && isYouTube(prev.view.webContents.getURL())))
    prev.view.webContents.executeJavaScript(PIP_ON, true).catch(() => {});
  if (id === split) split = active; // clicking the right pane's tab swaps sides
  active = id;
  tabs.get(id).view?.webContents.executeJavaScript(PIP_OFF).catch(() => {});
  render();
}

function close(id) {
  const t = tabs.get(id);
  if (!t) return;
  const ids = [...tabs.keys()], i = ids.indexOf(id);
  const url = info(t).url;
  if (url && url !== HOME) closed.push(url);
  tabs.delete(id);
  if (t.view) { if (t.shown) win.contentView.removeChildView(t.view); t.view.webContents.close(); }
  if (id === split) split = null;
  if (!tabs.size) return newTab();
  if (id === active) {
    active = split ?? ids[i - 1] ?? ids[i + 1];
    if (active === split) split = null;
  }
  render();
}

// ponytail: sleeping drops in-page state (scroll, forms); a tab playing audio is never put to sleep.
function sleepIdle() {
  for (const [id, t] of tabs) {
    if (!t.view || t.shown || Date.now() - t.lastSeen < SLEEP_MS) continue;
    const wc = t.view.webContents;
    if (wc.isCurrentlyAudible()) { t.lastSeen = Date.now(); continue; }
    tabs.set(id, { ...info(t), favicon: t.favicon });
    wc.close();
  }
  state();
}

const wc = () => tabs.get(active).view.webContents;
const cmd = {
  newTab: () => newTab(),
  reopen: () => closed.length && newTab(closed.pop()),
  close: id => close(id ?? active),
  select: id => select(id),
  go: input => wc().loadURL(toUrl(input)),
  open: url => newTab(toUrl(url)),
  back: () => wc().navigationHistory.goBack(),
  fwd: () => wc().navigationHistory.goForward(),
  reload: () => wc().reload(),
  hardReload: () => wc().reloadIgnoringCache(),
  home: () => wc().loadURL(HOME),
  devtools: () => wc().toggleDevTools(),
  zoom: d => { const w = wc(); w.setZoomLevel(d ? w.getZoomLevel() + d * 0.5 : 0); toast(`Zoom ${Math.round(100 * 1.2 ** w.getZoomLevel())}%`); },
  split: () => {
    if (split != null) split = null;
    else {
      const other = [...tabs].filter(([id]) => id !== active).sort((a, b) => (b[1].lastSeen || 0) - (a[1].lastSeen || 0))[0];
      split = other ? other[0] : newTab(HOME, false);
    }
    render();
  },
  shot: async () => { clipboard.writeImage(await wc().capturePage()); toast('Captura copiada al portapapeles'); },
  // Debug pack: console errors + failed requests + a screenshot path, ready to paste into an AI.
  copyErrors: async () => {
    const t = tabs.get(active), w = wc(), errs = t.errors, net = t.net || [];
    if (!errs.length && !net.length) return toast('Sin errores en esta pestaña');
    const shot = await saveShot(await w.capturePage(), 'debug');
    clipboard.writeText([
      `Mi app en ${w.getURL()} («${w.getTitle()}») tiene estos problemas. Encuentra la causa y arréglala.`,
      errs.length && `\nErrores de consola:\n${errs.map((e, i) => `${i + 1}. ${e}`).join('\n')}`,
      net.length && `\nPeticiones fallidas:\n${net.map(n => `- ${n}`).join('\n')}`,
      `\nCaptura de la pantalla: ${shot}`,
    ].filter(Boolean).join('\n'));
    toast(`Paquete de depuración copiado (${errs.length + net.length})`);
  },
  pick: async () => {
    const w = wc();
    w.focus();
    toast('Haz clic en un elemento · Esc para cancelar');
    const p = await w.executeJavaScript(PICKER).catch(() => null);
    if (!p) return;
    const z = w.getZoomFactor(), r = p.rect;
    const rect = { x: Math.max(0, Math.round(r.x * z)), y: Math.max(0, Math.round(r.y * z)), width: Math.max(1, Math.round(r.width * z)), height: Math.max(1, Math.round(r.height * z)) };
    const shot = await saveShot(await w.capturePage(rect), 'elemento');
    clipboard.writeText([
      `Quiero cambiar este elemento de mi app (${p.url}):`,
      '',
      p.comp.name ? `Componente: ${p.comp.name}${p.comp.src ? ` (${p.comp.src})` : ''}` : null,
      `Selector: ${p.selector}`,
      `Tamaño: ${Math.round(r.width)}×${Math.round(r.height)} en viewport ${p.viewport}`,
      p.text ? `Texto: "${p.text}"` : null,
      p.styles ? `Estilos: ${p.styles}` : null,
      'HTML:', '```html', p.html, '```',
      `Captura del elemento: ${shot}`,
      '',
      'Cambio que quiero: ',
    ].filter(s => s != null).join('\n'));
    toast('Elemento copiado: pégalo en tu IA y escribe el cambio');
  },
  copyUrl: () => { clipboard.writeText(wc().getURL()); toast('URL copiada'); },
  bookmark: () => {
    const w = wc(), url = w.getURL();
    if (!/^https?:/.test(url)) return toast('Esta página no se puede guardar');
    const had = bookmarks.some(b => b.url === url);
    setBookmarks(had ? bookmarks.filter(b => b.url !== url) : [{ url, title: w.getTitle() || url, favicon: tabs.get(active).favicon || '' }, ...bookmarks]);
    toast(had ? 'Quitado de favoritos' : 'Guardado en favoritos');
  },
  import: name => importFrom(name),
  mute: id => { const w = tabs.get(id ?? active)?.view?.webContents; if (w) { w.setAudioMuted(!w.isAudioMuted()); state(); } },
  // Windows 10+ lets only the user pick the default browser, so open the right Settings page for Nova.
  makeDefault: () => {
    app.setAsDefaultProtocolClient('http');
    app.setAsDefaultProtocolClient('https');
    shell.openExternal(app.isPackaged ? 'ms-settings:defaultapps?registeredAppUser=Nova' : 'ms-settings:defaultapps');
    toast(app.isPackaged ? 'Elige Nova en la ventana de Windows' : 'Instala Nova con el instalador para poder elegirlo');
  },
  clearSite: async () => {
    const origin = new URL(wc().getURL()).origin;
    await session.defaultSession.clearStorageData({ origin });
    await session.defaultSession.clearCache();
    wc().reloadIgnoringCache();
    toast(`Datos de ${origin} borrados`);
  },
  find: ({ text, next, back }) => text ? wc().findInPage(text, { findNext: !!next, forward: !back }) : wc().stopFindInPage('clearSelection'),
  findStop: () => wc().stopFindInPage('clearSelection'),
  yt: key => {
    if (!(key in LABELS)) return;
    settings[key] = !settings[key];
    saveJSON('settings.json', settings);
    applyYouTubeAll();
    state();
    toast(`${LABELS[key]}: ${settings[key] ? 'activado' : 'desactivado'}`);
  },
  // Mini player in the tab strip
  mediaToggle: id => tabs.get(id)?.view?.webContents.executeJavaScript(
    `(() => { const m = [...document.querySelectorAll('video, audio')].find(m => m.currentSrc); if (m) m.paused ? m.play() : m.pause(); })()`, true).catch(() => {}),
  mediaNext: id => tabs.get(id)?.view?.webContents.executeJavaScript(`document.querySelector('.ytp-next-button')?.click()`, true).catch(() => {}),
  wrapped: () => newTab(WRAPPED),
  // Nova IA side panel
  ai: () => {
    aiOpen = !aiOpen;
    clearTimeout(aiIdle);
    if (aiOpen && !aiView) {
      aiView = new WebContentsView({ webPreferences: { preload: path.join(__dirname, 'preload.js') } });
      aiView.setBackgroundColor('#0e1017');
      keys(aiView.webContents);
      aiView.webContents.loadFile('ai.html');
    }
    // A closed panel keeps its model warm for 10 min, then frees the GPU memory.
    if (!aiOpen) aiIdle = setTimeout(() => { if (!aiOpen && aiView) { aiView.webContents.close(); aiView = null; } }, 10 * 60e3);
    render();
    if (aiOpen) aiView.webContents.focus();
  },
  aiStatus: async () => aiView?.webContents.send('ai-status', { ollama: await ensureOllama() }),
  aiContext: async () => {
    aiTab = active;
    const w = wc(), url = w.getURL();
    const ctx = isYouTube(url) && /[?&]v=/.test(url)
      ? { kind: 'video', ...(await w.executeJavaScript(TRANSCRIPT).catch(() => ({}))) }
      : url === HOME || !/^https?:/.test(url) ? { kind: 'none' }
      : { kind: 'page', ...(await w.executeJavaScript(PAGE_TEXT).catch(() => ({}))) };
    aiView?.webContents.send('ai-context', { url, ...ctx });
  },
  seek: s => {
    if (!tabs.has(aiTab)) return;
    select(aiTab);
    wc().executeJavaScript(`(() => { const v = document.querySelector('video'); if (v) { v.currentTime = ${Number(s) || 0}; v.play(); } })()`, true).catch(() => {});
  },
  openUrl: url => /^https:\/\//.test(url) && newTab(url),
  ytMenu: ({ x, y }) => Menu.buildFromTemplate(Object.entries(YT_LABELS).map(([k, label]) =>
    ({ label, type: 'checkbox', checked: settings[k], click: () => cmd.yt(k) }))).popup({ window: win, x: Math.round(x), y: Math.round(y) }),
  overlay: on => { overlay = on; render(); if (!on) wc().focus(); },
  palette: async () => {
    overlay = true; render();
    ui.webContents.focus();
    ui.webContents.send('palette', { history: history.slice(0, 500), servers, bookmarks });
    scanServers().then(() => ui.webContents.send('servers', servers));
  },
  // userGesture=true lets requestPictureInPicture run without a click inside the page
  pip: () => wc().executeJavaScript(
    `(() => { const v = [...document.querySelectorAll('video')].find(v => v.readyState > 0);
      return v && (document.pictureInPictureElement ? document.exitPictureInPicture() : v.requestPictureInPicture()); })()`, true).catch(() => {}),
};

// The library's own cache never expires, and YouTube's anti-adblock changes every few weeks,
// so lists older than a day are re-downloaded. Offline: stale lists beat none; first run offline: empty.
async function loadBlocker() {
  const file = path.join(USER, 'engine.bin');
  const age = await fs.stat(file).then(s => Date.now() - s.mtimeMs, () => Infinity);
  const cached = () => fs.readFile(file).then(b => ElectronBlocker.deserialize(b));
  if (age < 24 * 3600e3) return cached().catch(loadFresh);
  return loadFresh();
  async function loadFresh() {
    try {
      const b = await ElectronBlocker.fromPrebuiltFull(fetch);
      await fs.writeFile(file, b.serialize());
      return b;
    } catch { return cached().catch(() => ElectronBlocker.empty()); }
  }
}

async function restore() {
  try { history = JSON.parse(await fs.readFile(path.join(USER, 'history.json'), 'utf8')); } catch {}
  try { settings = { ...settings, ...JSON.parse(await fs.readFile(path.join(USER, 'settings.json'), 'utf8')) }; } catch {}
  try { bookmarks = JSON.parse(await fs.readFile(path.join(USER, 'bookmarks.json'), 'utf8')); } catch {}
  try { stats = JSON.parse(await fs.readFile(path.join(USER, 'stats.json'), 'utf8')); } catch {}
  try { icons = JSON.parse(await fs.readFile(path.join(USER, 'icons.json'), 'utf8')); for (const h in icons) if (!icons[h]) delete icons[h]; } catch {}
  const launchUrl = urlArg(process.argv);
  if (launchUrl) { await restoreSession(); return newTab(clean(launchUrl)); }
  if (await restoreSession()) return;
  newTab();
}

// Returns true when it reopened saved tabs.
async function restoreSession() {
  try {
    const s = JSON.parse(await fs.readFile(path.join(USER, 'session.json'), 'utf8'));
    const ids = s.tabs.filter(u => typeof u === 'string' && /^(https?|file):/.test(u)).map(u => {
      const id = nextId++;
      tabs.set(id, { url: u, title: u, favicon: '' }); // restored asleep: zero cost until clicked
      return id;
    });
    if (ids.length) { select(ids[Math.min(s.active, ids.length - 1)] ?? ids[0]); return true; }
  } catch {} // first run or corrupt file
  return false;
}

// Updates come from GitHub Releases (see "publish" in package.json). Only the installed build updates itself.
function autoUpdate() {
  if (!app.isPackaged) return;
  const { autoUpdater } = require('electron-updater');
  autoUpdater.logger = null; // a missing release (404) is normal until the first one is published
  autoUpdater.on('update-downloaded', i => toast(`Nova ${i.version} lista: se instalará al cerrar`));
  autoUpdater.on('error', () => {}); // offline or no releases yet
  const check = () => autoUpdater.checkForUpdates().catch(() => {});
  check();
  setInterval(check, 6 * 3600e3);
}

app.whenReady().then(async () => {
  if (!PRIMARY) return;
  USER = app.getPath('userData');
  const blocker = await loadBlocker();
  const ses = session.defaultSession;
  blocker.enableBlockingInSession(ses);
  blocker.on('request-blocked', () => { blocked++; month().blocked++; ui?.webContents.send('blocked', blocked); });

  // Electron grants every permission by default; deny all but harmless ones. Local dev hosts get everything.
  // ponytail: no per-site prompt yet, so camera/mic on public sites (Meet, Zoom web) won't work. Add a prompt bar when needed.
  const SAFE = new Set(['fullscreen', 'pointerLock', 'clipboard-sanitized-write', 'speaker-selection']);
  ses.setPermissionRequestHandler((_wc, perm, done, d) => done(SAFE.has(perm) || isLocal(d.requestingUrl)));
  ses.setPermissionCheckHandler((_wc, perm, origin) => SAFE.has(perm) || isLocal(origin));
  ses.setDevicePermissionHandler(d => isLocal(d.origin)); // WebHID/USB/Serial only for local dev
  // Self-signed certs are normal for local HTTPS dev servers; everywhere else a bad cert is refused.
  app.on('certificate-error', (e, _wc, url, _err, _cert, cb) => { if (isLocal(url)) { e.preventDefault(); cb(true); } else cb(false); });
  app.on('web-contents-created', (_e, c) => c.on('will-attach-webview', e => e.preventDefault()));

  // Failed requests feed the debug pack, only on local dev tabs (public sites would drown it in tracker 4xx).
  // onCompleted/onErrorOccurred are free; the ad blocker owns onBeforeRequest/onHeadersReceived.
  const netFail = (d, msg) => {
    const t = [...tabs.values()].find(t => t.view && t.view.webContents.id === d.webContentsId);
    if (!t || t.net.length >= 50 || !isLocal(t.view.webContents.getURL())) return;
    t.net.push(`${msg} ${d.method} ${d.url}`);
    state();
  };
  ses.webRequest.onCompleted(d => { if (d.statusCode >= 400) netFail(d, `HTTP ${d.statusCode}`); });
  ses.webRequest.onErrorOccurred(d => {
    if (!/ERR_(BLOCKED_BY_CLIENT|ABORTED)/.test(d.error)) netFail(d, d.error);
  });

  win = new BaseWindow({
    width: 1360, height: 860, minWidth: 640, minHeight: 400, backgroundColor: '#0a0b10', title: 'Nova',
    titleBarStyle: 'hidden', titleBarOverlay: { color: '#0a0b10', symbolColor: '#c9cbe0', height: 38 },
    icon: nativeImage.createFromPath(path.join(__dirname, 'build', 'icon.png')),
  });
  app.on('second-instance', (_e, argv) => {
    const u = urlArg(argv);
    if (u) newTab(clean(u)); else newTab();
    if (win.isMinimized()) win.restore();
    win.focus();
  });
  ui = new WebContentsView({ webPreferences: { preload: path.join(__dirname, 'preload.js') } });
  ui.setBackgroundColor('#00000000'); // transparent so the palette can dim the page behind it
  win.contentView.addChildView(ui);
  keys(ui.webContents);
  ui.webContents.loadFile('ui.html');
  ui.webContents.once('did-finish-load', restore);
  win.on('resize', layout);
  win.on('close', () => {
    const sync = require('fs');
    sync.writeFileSync(path.join(USER, 'session.json'), JSON.stringify({ tabs: [...tabs.values()].map(t => info(t).url), active: [...tabs.keys()].indexOf(active) }));
    sync.writeFileSync(path.join(USER, 'history.json'), JSON.stringify(history));
    sync.writeFileSync(path.join(USER, 'stats.json'), JSON.stringify(stats));
  });
  setInterval(() => { sleepIdle(); saveJSON('stats.json', stats); refreshHomes(); }, 60e3);
  autoUpdate();

  ipcMain.on('cmd', (_e, name, arg) => cmd[name]?.(arg));
});

app.on('window-all-closed', () => app.quit());
