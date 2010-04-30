------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with Ada.Real_Time;

package body Time_Types is
   Start : constant Ada.Real_Time.Time := Ada.Real_Time.Clock;

   function Now return Time is
      use type Ada.Real_Time.Time;
   begin
      return Time
        (Ada.Real_Time.To_Duration (Ada.Real_Time.Clock - Start) * 1000);
   end Now;
end Time_Types;
