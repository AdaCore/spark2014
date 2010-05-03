------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

package body AIP.Timers is

   function Timer_Fired
     (Now : Time_Types.Time;
      TID : Timer_Id) return Boolean
   is
      pragma Unreferenced (Now);
      function C_Timer_Fired (TID : Timer_Id) return Boolean;
      pragma Import (C, C_Timer_Fired, "timer_testclr_evt");
   begin
      return C_Timer_Fired (TID);
   end Timer_Fired;

end AIP.Timers;
