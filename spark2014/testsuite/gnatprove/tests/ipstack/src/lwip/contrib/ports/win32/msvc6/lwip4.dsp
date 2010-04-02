# Microsoft Developer Studio Project File - Name="lwip4" - Package Owner=<4>
# Microsoft Developer Studio Generated Build File, Format Version 6.00
# ** NICHT BEARBEITEN **

# TARGTYPE "Win32 (x86) Static Library" 0x0104

CFG=lwip4 - Win32 Debug
!MESSAGE Dies ist kein gültiges Makefile. Zum Erstellen dieses Projekts mit NMAKE
!MESSAGE verwenden Sie den Befehl "Makefile exportieren" und führen Sie den Befehl
!MESSAGE 
!MESSAGE NMAKE /f "lwip4.mak".
!MESSAGE 
!MESSAGE Sie können beim Ausführen von NMAKE eine Konfiguration angeben
!MESSAGE durch Definieren des Makros CFG in der Befehlszeile. Zum Beispiel:
!MESSAGE 
!MESSAGE NMAKE /f "lwip4.mak" CFG="lwip4 - Win32 Debug"
!MESSAGE 
!MESSAGE Für die Konfiguration stehen zur Auswahl:
!MESSAGE 
!MESSAGE "lwip4 - Win32 Release" (basierend auf  "Win32 (x86) Static Library")
!MESSAGE "lwip4 - Win32 Debug" (basierend auf  "Win32 (x86) Static Library")
!MESSAGE 

# Begin Project
# PROP AllowPerConfigDependencies 0
# PROP Scc_ProjName ""
# PROP Scc_LocalPath ""
CPP=cl.exe
RSC=rc.exe

!IF  "$(CFG)" == "lwip4 - Win32 Release"

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

!ELSEIF  "$(CFG)" == "lwip4 - Win32 Debug"

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
# ADD LIB32 /nologo /out:"Debug\lwip4_d.lib"

!ENDIF 

# Begin Target

# Name "lwip4 - Win32 Release"
# Name "lwip4 - Win32 Debug"
# Begin Group "source"

# PROP Default_Filter "cpp;c;cxx;rc;def;r;odl;idl;hpj;bat"
# Begin Group "arch"
# Begin Source File

SOURCE="..\sys_arch.c"
# End Source File
# End Group
# Begin Group "api"
# Begin Source File

SOURCE="$(LWIP_DIR)\src\api\api_lib.c"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\api\api_msg.c"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\api\err.c"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\api\netbuf.c"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\api\netdb.c"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\api\netifapi.c"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\api\sockets.c"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\api\tcpip.c"
# End Source File
# End Group
# Begin Group "core"
# Begin Group "ipv4"
# Begin Source File

SOURCE="$(LWIP_DIR)\src\core\ipv4\autoip.c"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\core\ipv4\icmp.c"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\core\ipv4\igmp.c"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\core\ipv4\ip.c"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\core\ipv4\inet.c"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\core\ipv4\inet_chksum.c"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\core\ipv4\ip_addr.c"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\core\ipv4\ip_frag.c"
# End Source File
# End Group
# Begin Group "snmp"
# Begin Source File

SOURCE="$(LWIP_DIR)\src\core\snmp\asn1_dec.c"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\core\snmp\asn1_enc.c"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\core\snmp\mib_structs.c"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\core\snmp\mib2.c"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\core\snmp\msg_in.c"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\core\snmp\msg_out.c"
# End Source File
# End Group
# Begin Source File

SOURCE="$(LWIP_DIR)\src\core\dhcp.c"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\core\dns.c"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\core\init.c"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\core\mem.c"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\core\memp.c"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\core\netif.c"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\core\pbuf.c"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\core\raw.c"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\core\stats.c"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\core\sys.c"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\core\tcp.c"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\core\tcp_in.c"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\core\tcp_out.c"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\core\udp.c"
# End Source File
# End Group
# End Group
# Begin Group "header"

# PROP Default_Filter "h;hpp;hxx;hm;inl"
# Begin Group "core"
# Begin Group "ipv4"
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\ipv4\lwip\autoip.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\ipv4\lwip\icmp.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\ipv4\lwip\igmp.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\ipv4\lwip\inet.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\ipv4\lwip\inet_chksum.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\ipv4\lwip\ip.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\ipv4\lwip\ip_addr.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\ipv4\lwip\ip_frag.h"
# End Source File
# End Group
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\lwip\api.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\lwip\api_msg.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\lwip\arch.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\lwip\debug.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\lwip\def.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\lwip\dhcp.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\lwip\dns.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\lwip\err.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\lwip\init.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\lwip\mem.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\lwip\memp.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\lwip\memp_std.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\lwip\netbuf.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\lwip\netdb.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\lwip\netif.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\lwip\netifapi.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\lwip\opt.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\lwip\pbuf.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\lwip\raw.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\lwip\sio.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\lwip\snmp.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\lwip\snmp_asn1.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\lwip\snmp_msg.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\lwip\snmp_structs.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\lwip\sockets.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\lwip\stats.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\lwip\sys.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\lwip\tcp.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\lwip\tcpip.h"
# End Source File
# Begin Source File

SOURCE="$(LWIP_DIR)\src\include\lwip\udp.h"
# End Source File
# End Group

# Begin Group "arch"
# Begin Source File

SOURCE=..\include\arch\bpstruct.h
# End Source File
# Begin Source File

SOURCE=..\include\arch\cc.h
# End Source File
# Begin Source File

SOURCE=..\include\arch\epstruct.h
# End Source File
# Begin Source File

SOURCE=..\include\arch\perf.h
# End Source File
# Begin Source File

SOURCE=..\include\arch\sys_arch.h
# End Source File
# End Group

# Begin Group "port"
# Begin Source File

SOURCE=..\lwipopts.h
# End Source File
# Begin Source File

SOURCE=..\lwipcfg_msvc.h
# End Source File
# End Group

# End Group
# End Target
# End Project
