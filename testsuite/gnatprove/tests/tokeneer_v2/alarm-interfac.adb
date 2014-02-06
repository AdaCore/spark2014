------------------------------------------------------------------
-- Tokeneer ID Station Core Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency.All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd.under contract to the National Security Agency.
------------------------------------------------------------------

------------------------------------------------------------------
-- Alarm.Interfac
--
-- Implementation Notes:
--    None
--
------------------------------------------------------------------
with AlarmAPI;

package body Alarm.Interfac
  with SPARK_Mode => Off
is
   Is_Alarming : Boolean;

   function IsAlarming return Boolean is (Is_Alarming);

   ------------------------------------------------------------------
   -- Activate
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure Activate is
   begin
      AlarmAPI.Activate;
      Is_Alarming := True;
   end Activate;

   ------------------------------------------------------------------
   -- Deactivate
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure Deactivate is
   begin
      AlarmAPI.Deactivate;
      Is_Alarming := False;
   end Deactivate;

end Alarm.Interfac;
