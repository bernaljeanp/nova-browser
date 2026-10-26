const { contextBridge, ipcRenderer } = require('electron');

contextBridge.exposeInMainWorld('nova', {
  cmd: (name, arg) => ipcRenderer.send('cmd', name, arg),
  on: (ch, fn) => ipcRenderer.on(ch, (_e, data) => fn(data)),
});
