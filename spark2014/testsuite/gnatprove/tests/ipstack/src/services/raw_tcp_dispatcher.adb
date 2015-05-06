------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with RAW_TCP_Callbacks;

package body RAW_TCP_Dispatcher is

   use type AIP.Callbacks.CBK_Id;

   procedure TCP_Event
     (Ev   : AIP.TCP.TCP_Event_T;
      PCB  : AIP.PCBs.PCB_Id;
      Cbid : AIP.Callbacks.CBK_Id;
      Err  : out AIP.Err_T)
   is
   begin
      if Cbid /= AIP.Callbacks.NOCB then
         RAW_TCP_Callbacks.To_Hook (Cbid).all (Ev, PCB, Err);
      end if;
   end TCP_Event;

end RAW_TCP_Dispatcher;
