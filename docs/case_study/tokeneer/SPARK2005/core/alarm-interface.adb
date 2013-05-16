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
-- Alarm.Interface
--
-- Implementation Notes:
--    None
--
------------------------------------------------------------------
with AlarmAPI;

package body Alarm.Interface
is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------


   ------------------------------------------------------------------
   -- Activate
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------

   procedure Activate
   is
   begin
      AlarmAPI.Activate;
   end Activate;


   ------------------------------------------------------------------
   -- Deactivate
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------

   procedure Deactivate
   is
   begin
      AlarmAPI.Deactivate;
   end Deactivate;

end Alarm.Interface;
