------------------------------------------------------------------
-- Tokeneer ID Station Support Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency.All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd.under contract to the National Security Agency.
------------------------------------------------------------------

------------------------------------------------------------------
-- AlarmAPI
--
-- Description:
--    Alarm Interface.Provides facilities to activate and deactivate the
--    alarm.
--
------------------------------------------------------------------

package AlarmAPI is

   ------------------------------------------------------------------
   -- Activate
   --
   -- Description:
   --    Activates the alarm.
   --
   ------------------------------------------------------------------
   procedure Activate with Global => null;

   ------------------------------------------------------------------
   -- Deactivate
   --
   -- Description:
   --    Deactivates the alarm.
   --
   ------------------------------------------------------------------
   procedure Deactivate with Global => null;


end AlarmAPI;
