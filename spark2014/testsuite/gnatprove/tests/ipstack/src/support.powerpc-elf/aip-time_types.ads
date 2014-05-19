------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2014, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

package AIP.Time_Types is

   type Time is mod 2 ** 32;
   subtype Interval is Time;

   Clock_Hz : constant := 66_000_000;
   --  Number of cycles of the CPU cycle counter per second

   Hz : constant Interval := 1_000;
   --  Number of Time units per second

   function Now return Time;
   --  Elapsed time since unspecified epoch, in 1/Hz units

end AIP.Time_Types;
