------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--         Copyright (C) 2010-2014, Free Software Foundation, Inc.          --
------------------------------------------------------------------------------

with AIP.PCBs;
with AIP.UDP;
limited with AIP.Pools;

--  This unit implements a simplified syslog service over UDP using the RAW
--  API. The service accepts bare string application messages on the well
--  known syslog port (514) and forwards them as real user.debug syslog data
--  to a full fledged syslog server.

package RAW_UDP_Syslog is

   procedure SYSLOG_Process_Recv
     (Ev : AIP.UDP.UDP_Event_T; Pcb : AIP.PCBs.PCB_Id)
   --  Process UDP_RECV event EV for a syslog service bound to PCB
   with
     Global  => (In_Out => AIP.Pools.PBUF_POOL);

   procedure Init;
   --  Initialize the simplified syslog service

end RAW_UDP_Syslog;
