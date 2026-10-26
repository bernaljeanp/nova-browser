; Registers Nova as a browser so Windows lists it under Settings > Default apps.
; Windows 10+ never lets an installer set the default itself; the user picks Nova there.

!macro customInstall
  WriteRegStr SHCTX "Software\Clients\StartMenuInternet\Nova" "" "Nova"
  WriteRegStr SHCTX "Software\Clients\StartMenuInternet\Nova\DefaultIcon" "" "$INSTDIR\Nova.exe,0"
  WriteRegStr SHCTX "Software\Clients\StartMenuInternet\Nova\shell\open\command" "" '"$INSTDIR\Nova.exe"'
  WriteRegStr SHCTX "Software\Clients\StartMenuInternet\Nova\Capabilities" "ApplicationName" "Nova"
  WriteRegStr SHCTX "Software\Clients\StartMenuInternet\Nova\Capabilities" "ApplicationDescription" "Navegador ligero, sin anuncios ni rastreadores"
  WriteRegStr SHCTX "Software\Clients\StartMenuInternet\Nova\Capabilities" "ApplicationIcon" "$INSTDIR\Nova.exe,0"
  WriteRegStr SHCTX "Software\Clients\StartMenuInternet\Nova\Capabilities\StartMenu" "StartMenuInternet" "Nova"
  WriteRegStr SHCTX "Software\Clients\StartMenuInternet\Nova\Capabilities\URLAssociations" "http" "NovaURL"
  WriteRegStr SHCTX "Software\Clients\StartMenuInternet\Nova\Capabilities\URLAssociations" "https" "NovaURL"
  WriteRegStr SHCTX "Software\Clients\StartMenuInternet\Nova\Capabilities\FileAssociations" ".htm" "NovaURL"
  WriteRegStr SHCTX "Software\Clients\StartMenuInternet\Nova\Capabilities\FileAssociations" ".html" "NovaURL"
  WriteRegStr SHCTX "Software\RegisteredApplications" "Nova" "Software\Clients\StartMenuInternet\Nova\Capabilities"
  WriteRegStr SHCTX "Software\Classes\NovaURL" "" "Nova HTML Document"
  WriteRegStr SHCTX "Software\Classes\NovaURL\DefaultIcon" "" "$INSTDIR\Nova.exe,0"
  WriteRegStr SHCTX "Software\Classes\NovaURL\shell\open\command" "" '"$INSTDIR\Nova.exe" "%1"'
!macroend

!macro customUnInstall
  DeleteRegKey SHCTX "Software\Clients\StartMenuInternet\Nova"
  DeleteRegValue SHCTX "Software\RegisteredApplications" "Nova"
  DeleteRegKey SHCTX "Software\Classes\NovaURL"
!macroend
