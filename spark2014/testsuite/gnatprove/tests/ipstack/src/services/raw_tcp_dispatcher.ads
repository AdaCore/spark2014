------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Callbacks;
with AIP.PCBs;
with AIP.TCP;

package RAW_TCP_Dispatcher is

   procedure TCP_Event
     (Ev   : AIP.TCP.TCP_Event_T;
      PCB  : AIP.PCBs.PCB_Id;
      Cbid : AIP.Callbacks.CBK_Id;
      Err  : out AIP.Err_T);
   --  Process TCP event EV, aimed at PCB and for which Cbid was
   --  registered.

   pragma Export (Ada, TCP_Event, "AIP_tcp_event");

end RAW_TCP_Dispatcher;
