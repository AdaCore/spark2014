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
-- Alarm
--
-- Implementation Notes:
--    None
--
------------------------------------------------------------------

with Alarm.Interfac,
     AlarmTypes,
     AuditLog,
     AuditTypes,
     Door;
use type AlarmTypes.StatusT;

package body Alarm
--# own Output is out Alarm.Interfac.Output;
is pragma SPARK_Mode (On);

   function IsAlarming return Boolean is
   begin
      return Alarm.Interfac.IsAlarming;
   end IsAlarming;

   ------------------------------------------------------------------
   -- UpdateDevice
   --
   -- Implementation Notes:
   --    Makes appropriate call to private child.
   --
   ------------------------------------------------------------------

   procedure UpdateDevice
   --# global    out Interfac.Output;
   --#        in     Door.State;
   --#        in     AuditLog.State;
   --# derives Interfac.Output from Door.State,
   --#                               AuditLog.State;
   --# post
   --#      --------------------------------------------------------
   --#      -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
   --#      --====================================================--
   --#      -- After each call to UpdateDevice, the Alarm is      --
   --#      -- alarming if the conditions of the security         --
   --#      -- property hold. Note that from the Door package     --
   --#      -- annotation, Door.TheDoorAlarm = Alarming is        --
   --#      -- equivalent to the security property conditions     --
   --#      --------------------------------------------------------
   --#      Door.TheDoorAlarm(Door.State) = AlarmTypes.Alarming ->
   --#      Interfac.prf_isAlarming(Interfac.Output);
   is
      pragma Postcondition
        ((Door.TheDoorAlarm = AlarmTypes.Alarming) <=
         Interfac.IsAlarming);
   begin
      if Door.TheDoorAlarm = AlarmTypes.Alarming or
           AuditLog.TheAuditAlarm = AlarmTypes.Alarming then
         Interfac.Activate;
      else
         Interfac.Deactivate;
      end if;
   end UpdateDevice;

end Alarm;
