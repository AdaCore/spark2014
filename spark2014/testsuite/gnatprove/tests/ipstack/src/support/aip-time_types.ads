------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--# inherit AIP;

package AIP.Time_Types is
   type Time is mod 2 ** 32;
   subtype Interval is Time;

   Hz : constant := 1_000;
   --  Number of Time units per second

   function Now return Time;
   --  Elapsed time since unspecified epoch, in ms
   --  Should this be specified as "in Hz units"???

end AIP.Time_Types;
