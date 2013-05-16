------------------------------------------------------------------
-- Tokeneer ID Station Core Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency. All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd. under contract to the National Security Agency.
------------------------------------------------------------------

------------------------------------------------------------------
-- Clock.Interface
--
-- Description:
--    Interface to the system clock.
--
------------------------------------------------------------------
with Clock;
--# inherit Clock;

private package Clock.Interface
--# own in Now;
is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------


   ------------------------------------------------------------------
   -- TheTime
   --
   -- Description:
   --    returns the current time from the system clock.
   --
   ------------------------------------------------------------------
   function TheTime return Clock.TimeT;
   --# global in Now;

   ------------------------------------------------------------------
   -- AddDuration
   --
   -- Description:
   --    Adds a duration to a time.
   --
   ------------------------------------------------------------------
   function AddDuration ( T : Clock.TimeT ; D : Clock.DurationT )
                         return Clock.TimeT;

   ------------------------------------------------------------------
   -- IsValidTime
   --
   -- Description:
   --    Uses system calls to check that the supplied time is valid.
   --
   ------------------------------------------------------------------
   function IsValidTime ( T : Clock.TimeT ) return Boolean;

end Clock.Interface;
