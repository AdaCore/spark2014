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
-- Alarm
--
-- Implementation Notes:
--    None
--
------------------------------------------------------------------

with Alarm.Interfac,
     AlarmTypes,
     AuditTypes,
     Door;
use type AlarmTypes.StatusT;

package body Alarm
  with SPARK_Mode,
       Refined_State => (Output => Alarm.Interfac.Output)
is
   function IsAlarming return Boolean is (Alarm.Interfac.IsAlarming);

   ------------------------------------------------------------------
   -- UpdateDevice
   --
   -- Implementation Notes:
   --    Makes appropriate call to private child.
   --
   ------------------------------------------------------------------

   procedure UpdateDevice
     with Refined_Global  => (Input  => (AuditLog.State,
                                         Door.State),
                              Output => Interfac.Output),
          Refined_Depends => (Interfac.Output => (AuditLog.State,
                                                  Door.State)),
          Refined_Post    => (if Door.TheDoorAlarm = AlarmTypes.Alarming then
                               Interfac.IsAlarming)
      --------------------------------------------------------
      -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
      --====================================================--
      -- After each call to UpdateDevice, the Alarm is      --
      -- alarming if the conditions of the security         --
      -- property hold.Note that from the Door package      --
      -- annotation, Door.TheDoorAlarm = Alarming is        --
      -- equivalent to the security property conditions     --
      --------------------------------------------------------
   is
   begin
      if Door.TheDoorAlarm = AlarmTypes.Alarming or
           AuditLog.TheAuditAlarm = AlarmTypes.Alarming then
#if SECURITY_DEMO
         --  implementation flaw: deactive called instead of activate
         Interfac.Deactivate;
#else
         Interfac.Activate;
#end if;
      else
         Interfac.Deactivate;
      end if;
   end UpdateDevice;

end Alarm;
