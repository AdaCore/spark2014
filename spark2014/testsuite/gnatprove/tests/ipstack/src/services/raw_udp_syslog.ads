------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.UDP;

--# inherit AIP.Pools, AIP.IPaddrs, AIP.Pbufs, AIP.Inet,
--#         AIP.Callbacks, AIP.UDP, AIP.Conversions;

--  This unit implements a simplified syslog service over UDP using the RAW
--  API. The service accepts bare string application messages on the well
--  known syslog port (514) and forwards them as real user.debug syslog data
--  to a full fledged syslog server.

package RAW_UDP_Syslog is

   procedure SYSLOG_Process_Recv
     (Ev : AIP.UDP.UDP_Event_T; Pcb : AIP.UDP.PCB_Id);
   --  Process UDP_RECV event EV for a syslog service bound to PCB

   procedure Init;
   --  Initialize the simplified syslog service

end RAW_UDP_Syslog;
