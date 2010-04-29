------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

package PPC_Clock is
   type Cycle_Type is mod 2**64;
   function Get_Cycle_Counter return Cycle_Type;
end PPC_Clock;
