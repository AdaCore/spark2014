------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Callbacks;
with AIP.PCBs;
with AIP.UDP;

package RAW_UDP_Dispatcher is

   procedure UDP_Event
     (Ev   : AIP.UDP.UDP_Event_T;
      PCB  : AIP.PCBs.PCB_Id;
      Cbid : AIP.Callbacks.CBK_Id);
   --  Process UDP event EV, aimed at bound PCB, for which Cbid was
   --  registered.

   pragma Export (Ada, UDP_Event, "AIP_udp_event");

end RAW_UDP_Dispatcher;
