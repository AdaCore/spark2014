------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with RAW_UDP_Callbacks;
with RAW_UDP_Syslog;

package body RAW_UDP_Dispatcher is

   procedure UDP_Event
     (Ev   : AIP.UDP.UDP_Event_T;
      PCB  : AIP.PCBs.PCB_Id;
      Cbid : AIP.Callbacks.CBK_Id) is
   begin
      --  Note: in this example dispatcher, callback ids are arbitrary
      --  identifiers, and we use a case statement to dispatch to the
      --  appropriate routine. However the user could also decide to use
      --  directly each routine's address as the associated callback id,
      --  and implement the dispatcher as an unchecked conversion of callback
      --  id to access-to-subprogram followed by an indirect call.

      case Cbid is
         when RAW_UDP_Callbacks.SYSLOG_RECV =>
            RAW_UDP_Syslog.SYSLOG_Process_Recv (Ev, PCB);
         when others =>
            null;
      end case;
   end UDP_Event;

end RAW_UDP_Dispatcher;
