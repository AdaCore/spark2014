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
-- Door
--
-- Implementation Notes:
--    None
--
------------------------------------------------------------------
with Door.Interfac,
     AuditLog,
     AuditTypes,
     AlarmTypes,
     Clock,
     ConfigData,
     Latch;

use type AlarmTypes.StatusT;

package body Door
  with Refined_State => (State => (CurrentDoor,
                                   AlarmTimeout,
                                   DoorAlarm),
                         Input => Door.Interfac.Input)
is

   ------------------------------------------------------------------
   -- State
   ------------------------------------------------------------------
   CurrentDoor  : T;
   DoorAlarm    : AlarmTypes.StatusT;
   AlarmTimeout : Clock.TimeT;

   function Alarm_Timeout return Clock.TimeT is (AlarmTimeout)
     with Refined_Global => AlarmTimeout;

   ------------------------------------------------------------------
   -- UpdateDoorAlarm
   --
   -- Description:
   --    Local procedure that activates the alarm if the door is
   --    open/locked and the door alarm timeout has passed.
   --
   -- Implementation Notes:
   --    Used by Poll, LockDoor and UnlockDoor
   --
   -- Traceunit : C.Door.UpdateDoorAlarm
   -- Traceto   : FD.Latch.UpdateInternalAlarm
   ------------------------------------------------------------------
   procedure UpdateDoorAlarm
     with Global  => (Input  => (AlarmTimeout,
                                 Clock.CurrentTime,
                                 Clock.Now,
                                 ConfigData.State,
                                 CurrentDoor,
                                 Latch.State),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 DoorAlarm)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AlarmTimeout,
                                               AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.CurrentTime,
                                               Clock.Now,
                                               ConfigData.State,
                                               CurrentDoor,
                                               DoorAlarm,
                                               Latch.State),
                      DoorAlarm            => (AlarmTimeout,
                                               Clock.CurrentTime,
                                               CurrentDoor,
                                               Latch.State)),
          --------------------------------------------------------
          -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
          --====================================================--
          -- After each call to UpdateDoorAlarm, the security   --
          -- property holds.                                    --
          --------------------------------------------------------
          Post    => (CurrentDoor = Open and
                      Latch.IsLocked and
                      Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
                                              AlarmTimeout)) =
                       (DoorAlarm = AlarmTypes.Alarming)

   is
      LocalAlarm : AlarmTypes.StatusT;
      Severity   : AuditTypes.SeverityT;
      ID         : AuditTypes.ElementT;
   begin
      if CurrentDoor = Open and
        Latch.IsLocked and
        Clock.GreaterThanOrEqual(Left  => Clock.TheCurrentTime,
                                 Right => AlarmTimeout)
      then
         LocalAlarm := AlarmTypes.Alarming;
         Severity   := AuditTypes.Critical;
         ID         := AuditTypes.AlarmRaised;
      else
         LocalAlarm := AlarmTypes.Silent;
         Severity   := AuditTypes.Information;
         ID         := AuditTypes.AlarmSilenced;
      end if;

      if DoorAlarm /= LocalAlarm then
         AuditLog.AddElementToLog(
                ElementID    => ID,
                Severity     => Severity,
                User         => AuditTypes.NoUser,
                Description  => AuditTypes.NoDescription
                );
      end if;

      DoorAlarm := LocalAlarm;

   end UpdateDoorAlarm;

   ------------------------------------------------------------------
   -- Poll
   --
   -- Implementation Notes:
   --    Clock must be polled before this is called.
   --
   ------------------------------------------------------------------
   procedure Poll (SystemFault :    out Boolean)
     with Refined_Global  => (Input  => (AlarmTimeout,
                                         Clock.CurrentTime,
                                         Clock.Now,
                                         ConfigData.State,
                                         Interfac.Input),
                              In_Out => (AuditLog.FileState,
                                         AuditLog.State,
                                         CurrentDoor,
                                         DoorAlarm,
                                         Latch.State)),
          Refined_Depends => ((AuditLog.FileState,
                               AuditLog.State)     => (AlarmTimeout,
                                                       AuditLog.FileState,
                                                       AuditLog.State,
                                                       Clock.CurrentTime,
                                                       Clock.Now,
                                                       ConfigData.State,
                                                       CurrentDoor,
                                                       DoorAlarm,
                                                       Interfac.Input,
                                                       Latch.State),
                              CurrentDoor          =>+ Interfac.Input,
                              DoorAlarm            => (AlarmTimeout,
                                                       Clock.CurrentTime,
                                                       CurrentDoor,
                                                       Interfac.Input,
                                                       Latch.State),
                              Latch.State          =>+ Clock.CurrentTime,
                              SystemFault          => Interfac.Input),
          --------------------------------------------------------
          -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
          --====================================================--
          -- After each call to Poll, the security property     --
          -- holds.                                             --
          --------------------------------------------------------
          Refined_Post    => ((CurrentDoor = Open and
                               Latch.IsLocked and
                               Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
                                                        AlarmTimeout)) =
                                 (DoorAlarm = AlarmTypes.Alarming))

                              and

                              (Latch.IsLocked =
                                 Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
                                                          Latch.Latch_Timeout))

                              and Latch.Latch_Timeout = Latch.Latch_Timeout'Old
   is
      NewDoor : T;
      ID      : AuditTypes.ElementT;
   begin
      Interfac.GetDoorState(DoorState => NewDoor,
                             Fault     => SystemFault);

      if SystemFault then

         -- Door is in error state - raise a critical system fault
         AuditLog.AddElementToLog(
                ElementID    => AuditTypes.SystemFault,
                Severity     => AuditTypes.Critical,
                User         => AuditTypes.NoUser,
                Description  => "DOOR STATE CANNOT BE DETERMINED"
                );

      else

         if CurrentDoor /= NewDoor then

            -- Door has changed - add event to log
            if NewDoor = Closed then
               ID := AuditTypes.DoorClosed;
            else
               ID := AuditTypes.DoorOpened;
            end if;

            AuditLog.AddElementToLog(
                                     ElementID    => ID,
                                     Severity     => AuditTypes.Information,
                                     User         => AuditTypes.NoUser,
                                     Description  => AuditTypes.NoDescription
                                    );

            CurrentDoor := NewDoor;

         end if;

         SystemFault := False;
      end if;

      Latch.UpdateInternalLatch;
      UpdateDoorAlarm;

   end Poll;

   ------------------------------------------------------------------
   -- UnlockDoor
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure UnlockDoor
     with Refined_Global  => (Input  => (Clock.CurrentTime,
                                         Clock.Now,
                                         ConfigData.State,
                                         CurrentDoor),
                              Output => AlarmTimeout,
                              In_Out => (AuditLog.FileState,
                                         AuditLog.State,
                                         DoorAlarm,
                                         Latch.State)),
          Refined_Depends => (AlarmTimeout         => (Clock.CurrentTime,
                                                       ConfigData.State),
                              (AuditLog.FileState,
                               AuditLog.State)     => (AuditLog.FileState,
                                                       AuditLog.State,
                                                       Clock.CurrentTime,
                                                       Clock.Now,
                                                       ConfigData.State,
                                                       CurrentDoor,
                                                       DoorAlarm,
                                                       Latch.State),
                              DoorAlarm            => (Clock.CurrentTime,
                                                       ConfigData.State,
                                                       CurrentDoor,
                                                       Latch.State),
                              Latch.State          =>+ (Clock.CurrentTime,
                                                        ConfigData.State)),
          --------------------------------------------------------
          -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
          --====================================================--
          -- After each call to UnlockDoor, the security        --
          -- property holds.                                    --
          --------------------------------------------------------
          Refined_Post    => ((CurrentDoor = Open and
                               Latch.IsLocked and
                               Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
                                                        AlarmTimeout)) =
                                (DoorAlarm = AlarmTypes.Alarming))

                             and

                             (Latch.IsLocked =
                                Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
                                                         Latch.Latch_Timeout))

   is
      LatchTimeout : Clock.TimeT;
   begin

      LatchTimeout := Clock.AddDuration(
                         TheTime     => Clock.TheCurrentTime,
                         TheDuration => ConfigData.TheLatchUnlockDuration
                         );

      Latch.SetTimeout(Time => LatchTimeout);

      AlarmTimeout := Clock.AddDuration(
                            TheTime     => LatchTimeout,
                            TheDuration => ConfigData.TheAlarmSilentDuration
                            );

      Latch.UpdateInternalLatch;
      UpdateDoorAlarm;

   end UnlockDoor;

   ------------------------------------------------------------------
   -- LockDoor
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure LockDoor
     with Refined_Global  => (Input  => (Clock.CurrentTime,
                                         Clock.Now,
                                         ConfigData.State,
                                         CurrentDoor),
                              Output => AlarmTimeout,
                              In_Out => (AuditLog.FileState,
                                         AuditLog.State,
                                         DoorAlarm,
                                         Latch.State)),
          Refined_Depends => (AlarmTimeout         => Clock.CurrentTime,
                              (AuditLog.FileState,
                               AuditLog.State)     => (AuditLog.FileState,
                                                       AuditLog.State,
                                                       Clock.CurrentTime,
                                                       Clock.Now,
                                                       ConfigData.State,
                                                       CurrentDoor,
                                                       DoorAlarm,
                                                       Latch.State),
                              DoorAlarm            => (Clock.CurrentTime,
                                                       CurrentDoor,
                                                       Latch.State),
                              Latch.State          =>+ Clock.CurrentTime),
          --------------------------------------------------------
          -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
          --====================================================--
          -- After each call to LockDoor, the security property --
          -- holds.                                             --
          --------------------------------------------------------
          Refined_Post    => ((CurrentDoor = Open and
                               Latch.IsLocked and
                               Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
                                                        AlarmTimeout)) =
                                 (DoorAlarm = AlarmTypes.Alarming)) and
                             Latch.IsLocked
   is
   begin

      Latch.SetTimeout(Time => Clock.TheCurrentTime);
      AlarmTimeout := Clock.TheCurrentTime;

      Latch.UpdateInternalLatch;
      UpdateDoorAlarm;

   end LockDoor;

   ------------------------------------------------------------------
   -- Init
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure Init
     with Refined_Global  => (Output => (AlarmTimeout,
                                         CurrentDoor,
                                         DoorAlarm)),
          Refined_Depends => ((AlarmTimeout,
                               CurrentDoor,
                               DoorAlarm)    => null)
   is
   begin
      CurrentDoor  := Closed;
      DoorAlarm    := AlarmTypes.Silent;
      AlarmTimeout := Clock.ZeroTime;
   end Init;

   ------------------------------------------------------------------
   -- TheCurrentDoor
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   function TheCurrentDoor return T is (CurrentDoor)
     with Refined_Global => CurrentDoor;

   ------------------------------------------------------------------
   -- TheDoorAlarm
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   function TheDoorAlarm return AlarmTypes.StatusT is (DoorAlarm)
     with Refined_Global => DoorAlarm;

   ------------------------------------------------------------------
   -- Failure
   --
   -- Implementation notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure Failure
     with Refined_Global  => (Output => (AlarmTimeout,
                                         CurrentDoor,
                                         DoorAlarm,
                                         Latch.State)),
          Refined_Depends => ((AlarmTimeout,
                               CurrentDoor,
                               DoorAlarm,
                               Latch.State)  => null)
   is
   begin
      CurrentDoor  := Open;
      AlarmTimeout := Clock.ZeroTime;
      DoorAlarm    := AlarmTypes.Alarming;
      Latch.Failure;
   end Failure;

end Door;
