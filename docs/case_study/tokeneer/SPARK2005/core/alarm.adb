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

with Alarm.Interface,
     AlarmTypes,
     AuditLog,
     AuditTypes,
     Door;
use type AlarmTypes.StatusT;

package body Alarm
--# own Output is out Alarm.Interface.Output;
is

   ------------------------------------------------------------------
   -- UpdateDevice
   --
   -- Implementation Notes:
   --    Makes appropriate call to private child.
   --
   ------------------------------------------------------------------

   procedure UpdateDevice
   --# global    out Interface.Output;
   --#        in     Door.State;
   --#        in     AuditLog.State;
   --# derives Interface.Output from Door.State,
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
   --#      Interface.prf_isAlarming(Interface.Output);
   is
   begin
      if Door.TheDoorAlarm = AlarmTypes.Alarming or
           AuditLog.TheAuditAlarm = AlarmTypes.Alarming then
         Interface.Activate;
      else
         Interface.Deactivate;
      end if;
   end UpdateDevice;

end Alarm;
