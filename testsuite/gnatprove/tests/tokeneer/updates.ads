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
-- Updates
--
-- Description:
--    Utility package responsible for performing updates of the
--    environment.
--
------------------------------------------------------------------
with Admin,
     Alarm,
     AlarmTypes,
     AuditLog,
     Clock,
     ConfigData,
     Display,
     Door,
     Latch,
     Screen,
     Stats;

use Alarm,
    AlarmTypes,
    Door,
    Latch;

package Updates is
   ------------------------------------------------------------------
   -- EarlyActivity
   --
   -- Description:
   --    Performs the critical updates of the latch and the alarm.
   --
   -- Traceunit: C.Updates.EarlyActivity
   -- Traceto: FD.Interfac.TISEarlyUpdates
   ------------------------------------------------------------------
   procedure EarlyActivity (SystemFault :    out Boolean)
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State,
                                 Door.State,
                                 Latch.State),
                      Output => (Alarm.Output,
                                 Latch.Output),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State)),
          Depends => (Alarm.Output         => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Door.State,
                                               Latch.State),
                      (AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Latch.State),
                      (Latch.Output,
                       SystemFault)        => Latch.State),
          --------------------------------------------------------
          -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
          --====================================================--
          -- After each call to EarlyActivity, the Alarm is     --
          -- alarming if the conditions of the security         --
          -- property hold.                                     --
          -- Note that from the Door package annotation,        --
          -- Door.TheDoorAlarm = Alarming is equivalent to the  --
          -- security property conditions                       --
          --------------------------------------------------------
          Post    => (if Door.TheDoorAlarm = AlarmTypes.Alarming then
                         Alarm.isAlarming) and
                     ((Latch.IsLocked = Latch.LatchIsLocked) or
                        SystemFault);

   ------------------------------------------------------------------
   -- Activity
   --
   -- Description:
   --    Performs the updates performed at the end of a processing cycle.
   --
   -- Traceunit: C.Updates.Activity
   -- Traceto: FD.Interfac.TISUpdates
   ------------------------------------------------------------------
   procedure Activity (TheStats    : in     Stats.T;
                       TheAdmin    : in     Admin.T;
                       SystemFault :    out Boolean)
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State,
                                 Door.State,
                                 Latch.State),
                      Output => (Alarm.Output,
                                 Latch.Output,
                                 Screen.Output),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 Display.Output,
                                 Display.State,
                                 Screen.State)),
          Depends => ((Alarm.Output,
                       AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Display.State,
                                               Door.State,
                                               Latch.State,
                                               Screen.State,
                                               TheAdmin,
                                               TheStats),
                      Display.Output       =>+ Display.State,
                      Display.State        => Display.State,
                      (Latch.Output,
                       SystemFault)        => Latch.State,
                      (Screen.Output,
                       Screen.State)       => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Display.State,
                                               Door.State,
                                               Screen.State,
                                               TheAdmin,
                                               TheStats)),
          --------------------------------------------------------
          -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
          --====================================================--
          -- After each call to Activity, the Alarm is alarming --
          -- if the conditions of the security property hold.   --
          -- Note that from the Door package annotation,        --
          -- Door.TheDoorAlarm = Alarming is equivalent to the  --
          -- security property conditions                       --
          --------------------------------------------------------
          Post    => (if Door.TheDoorAlarm = AlarmTypes.Alarming then
                         Alarm.isAlarming) and
                     ((Latch.IsLocked = Latch.LatchisLocked) or
                        SystemFault);

end Updates;
