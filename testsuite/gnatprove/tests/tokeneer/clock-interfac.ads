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
-- Clock.Interfac
--
-- Description:
--    Interfac to the system clock.
--
------------------------------------------------------------------
with Clock;

private package Clock.Interfac
  with Abstract_State => (Now with External => Async_Writers,
                                   Part_Of => Clock.Now)
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
   function TheTime return Clock.TimeT
     with Volatile_Function,
          Global => Now;

   ------------------------------------------------------------------
   -- AddDuration
   --
   -- Description:
   --    Adds a duration to a time.
   --
   ------------------------------------------------------------------
   function AddDuration (T : Clock.TimeT ; D : Clock.DurationT)
                        return Clock.TimeT
     with Global => null;

   ------------------------------------------------------------------
   -- IsValidTime
   --
   -- Description:
   --    Uses system calls to check that the supplied time is valid.
   --
   ------------------------------------------------------------------
   function IsValidTime (T : Clock.TimeT) return Boolean
     with Global => null;

end Clock.Interfac;
