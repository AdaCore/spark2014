------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2012, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

--# inherit AIP;

package AIP.Time_Types is

   type Time is mod 2 ** 32;
   subtype Interval is Time;

   Hz : constant Interval := 1_000;
   --  Number of Time units per second

   function Now return Time;
   --  Elapsed time since unspecified epoch, in 1/Hz units

end AIP.Time_Types;
