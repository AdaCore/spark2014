# Microsoft Developer Studio Project File - Name="apps" - Package Owner=<4>
# Microsoft Developer Studio Generated Build File, Format Version 6.00
# ** NICHT BEARBEITEN **

# TARGTYPE "Win32 (x86) Static Library" 0x0104

CFG=apps - Win32 Debug
!MESSAGE Dies ist kein gültiges Makefile. Zum Erstellen dieses Projekts mit NMAKE
!MESSAGE verwenden Sie den Befehl "Makefile exportieren" und führen Sie den Befehl
!MESSAGE 
!MESSAGE NMAKE /f "apps.mak".
!MESSAGE 
!MESSAGE Sie können beim Ausführen von NMAKE eine Konfiguration angeben
!MESSAGE durch Definieren des Makros CFG in der Befehlszeile. Zum Beispiel:
!MESSAGE 
!MESSAGE NMAKE /f "apps.mak" CFG="apps - Win32 Debug"
!MESSAGE 
!MESSAGE Für die Konfiguration stehen zur Auswahl:
!MESSAGE 
!MESSAGE "apps - Win32 Release" (basierend auf  "Win32 (x86) Static Library")
!MESSAGE "apps - Win32 Debug" (basierend auf  "Win32 (x86) Static Library")
!MESSAGE 

# Begin Project
# PROP AllowPerConfigDependencies 0
# PROP Scc_ProjName ""
# PROP Scc_LocalPath ""
CPP=cl.exe
RSC=rc.exe

!IF  "$(CFG)" == "apps - Win32 Release"

# PROP BASE Use_MFC 0
# PROP BASE Use_Debug_Libraries 0
# PROP BASE Output_Dir "Release"
# PROP BASE Intermediate_Dir "Release"
# PROP BASE Target_Dir ""
# PROP Use_MFC 0
# PROP Use_Debug_Libraries 0
# PROP Output_Dir "Release"
# PROP Intermediate_Dir "Release"
# PROP Target_Dir ""
# ADD BASE CPP /nologo /W3 /GX /O2 /D "WIN32" /D "NDEBUG" /D "_MBCS" /D "_LIB" /YX /FD /c
# ADD CPP /nologo /W3 /GX /O2 /I "$(LWIP_DIR)\src\include" /I "$(LWIP_DIR)\src\include\ipv4" /I "..\include" /I "..\\" /D "WIN32" /D "NDEBUG" /D "_MBCS" /D "_LIB" /YX /FD /c
# ADD BASE RSC /l 0x407 /d "NDEBUG"
# ADD RSC /l 0x407 /d "NDEBUG"
BSC32=bscmake.exe
# ADD BASE BSC32 /nologo
# ADD BSC32 /nologo
LIB32=link.exe -lib
# ADD BASE LIB32 /nologo
# ADD LIB32 /nologo

!ELSEIF  "$(CFG)" == "apps - Win32 Debug"

# PROP BASE Use_MFC 0
# PROP BASE Use_Debug_Libraries 1
# PROP BASE Output_Dir "Debug"
# PROP BASE Intermediate_Dir "Debug"
# PROP BASE Target_Dir ""
# PROP Use_MFC 0
# PROP Use_Debug_Libraries 1
# PROP Output_Dir "Debug"
# PROP Intermediate_Dir "Debug"
# PROP Target_Dir ""
# ADD BASE CPP /nologo /W3 /Gm /GX /ZI /Od /D "WIN32" /D "_DEBUG" /D "_MBCS" /D "_LIB" /YX /FD /GZ /c
# ADD CPP /nologo /W3 /Gm /GX /ZI /Od /I "$(LWIP_DIR)\src\include" /I "$(LWIP_DIR)\src\include\ipv4" /I "..\include" /I "..\\" /D "_LIB" /D "WIN32" /D "_DEBUG" /D "_MBCS" /D "LWIP_DEBUG" /YX /FD /GZ /c
# ADD BASE RSC /l 0x407 /d "_DEBUG"
# ADD RSC /l 0x407 /d "_DEBUG"
BSC32=bscmake.exe
# ADD BASE BSC32 /nologo
# ADD BSC32 /nologo
LIB32=link.exe -lib
# ADD BASE LIB32 /nologo
# ADD LIB32 /nologo /out:"Debug\apps_d.lib"

!ENDIF 

# Begin Target

# Name "apps - Win32 Release"
# Name "apps - Win32 Debug"
# Begin Group "source"

# PROP Default_Filter "cpp;c;cxx;rc;def;r;odl;idl;hpj;bat"
# Begin Group "chargen"
# Begin Source File

SOURCE="..\..\..\apps\chargen\chargen.c"
# End Source File
# End Group
# Begin Group "httpserver"
# Begin Source File

SOURCE="..\..\..\apps\httpserver\httpserver-netconn.c"
# End Source File
# End Group
# Begin Group "httpserver_raw"
# Begin Source File

SOURCE="..\..\..\apps\httpserver_raw\fs.c"
# End Source File
# Begin Source File

SOURCE="..\..\..\apps\httpserver_raw\httpd.c"
# End Source File
# End Group
# Begin Group "netio"
# Begin Source File

SOURCE="..\..\..\apps\netio\netio.c"
# End Source File
# End Group
# Begin Group "netbios"
# Begin Source File

SOURCE="..\..\..\apps\netbios\netbios.c"
# End Source File
# End Group
# Begin Group "ping"
# Begin Source File

SOURCE="..\..\..\apps\ping\ping.c"
# End Source File
# End Group
# Begin Group "sntp"
# Begin Source File

SOURCE="..\..\..\apps\sntp\sntp.c"
# End Source File
# End Group
# End Group
# Begin Group "header"

# PROP Default_Filter "h;hpp;hxx;hm;inl"
# Begin Group "httpserver_raw"
# Begin Source File

SOURCE="..\..\..\apps\httpserver_raw\fs.h"
# End Source File
# Begin Source File

SOURCE="..\..\..\apps\httpserver_raw\fsdata.h"
# End Source File
# Begin Source File

SOURCE="..\..\..\apps\httpserver_raw\httpd.h"
# End Source File
# End Group
# Begin Group "netio"
# Begin Source File

SOURCE="..\..\..\apps\netio\netio.h"
# End Source File
# End Group
# Begin Group "netbios"
# Begin Source File

SOURCE="..\..\..\apps\netbios\netbios.h"
# End Source File
# End Group
# Begin Group "ping"
# Begin Source File

SOURCE="..\..\..\apps\sntp\sntp.h"
# End Source File
# End Group
# Begin Group "sntp"
# Begin Source File

SOURCE="..\..\..\apps\sntp\sntp.h"
# End Source File
# End Group
# End Group
# End Target
# End Project
