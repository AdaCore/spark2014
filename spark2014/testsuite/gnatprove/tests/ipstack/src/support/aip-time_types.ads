------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--# inherit AIP;

package AIP.Time_Types is

   type Time is mod 2 ** 32;
   subtype Interval is Time;

   function Now return Time;
   --  Elapsed time since unspecified epoch, in ms

end AIP.Time_Types;
