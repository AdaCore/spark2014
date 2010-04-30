------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with PPC_Clock;
package body Time_Types is
   function Now return Time is
      use type PPC_Clock.Cycle_Type;

      function Shift_Right
        (Value  : PPC_Clock.Cycle_Type;
         Amount : Natural) return PPC_Clock.Cycle_Type;
      pragma Import (Intrinsic, Shift_Right);

   begin
      return Time (Shift_Right (PPC_Clock.Get_Cycle_Counter, 16));
      --  Approximation: the PPC clock runs at 66 MHz, not 65.536
   end Now;
end Time_Types;
