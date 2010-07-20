------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with RAW_UDP_Callbacks, RAW_UDP_Syslog;

package body RAW_UDP_Dispatcher is

   procedure UDP_Event
     (Ev   : AIP.UDP.UDP_Event_T;
      Pcb  : AIP.UDP.PCB_Id;
      Cbid : AIP.Callbacks.CBK_Id) is
   begin
      case Cbid is
         when RAW_UDP_Callbacks.SYSLOG_RECV =>
            RAW_UDP_Syslog.SYSLOG_Process_Recv (Ev, Pcb);
         when others =>
            null;
      end case;
   end UDP_Event;

end RAW_UDP_Dispatcher;
