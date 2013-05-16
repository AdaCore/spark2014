------------------------------------------------------------------
-- Tokeneer ID Station Core Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency. All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd. under contract to the National Security Agency.
--
-- Modifications to proof annotations by Phil Thornley, April 2009
------------------------------------------------------------------

------------------------------------------------------------------
-- Door
--
-- Implementation Notes:
--    None
--
------------------------------------------------------------------
with Door.Interface,
     AuditLog,
     AuditTypes,
     AlarmTypes,
     Clock,
     ConfigData,
     Latch;

use type AlarmTypes.StatusT;

package body Door
--# own State is CurrentDoor,
--#              AlarmTimeout,
--#              DoorAlarm &
--#     Input is in Door.Interface.Input;
is

   ------------------------------------------------------------------
   -- State
   ------------------------------------------------------------------
   CurrentDoor  : T;
   DoorAlarm    : AlarmTypes.StatusT;
   AlarmTimeout : Clock.TimeT;


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
   --# global in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in     Clock.CurrentTime;
   --#        in     Latch.State;
   --#        in     AlarmTimeout;
   --#        in     CurrentDoor;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#        in out DoorAlarm;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 Clock.CurrentTime,
   --#                                 Latch.State,
   --#                                 DoorAlarm,
   --#                                 AlarmTimeout,
   --#                                 CurrentDoor &
   --#         DoorAlarm          from Clock.CurrentTime,
   --#                                 Latch.State,
   --#                                 AlarmTimeout,
   --#                                 CurrentDoor;
   --# post
   --#      --------------------------------------------------------
   --#      -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
   --#      --====================================================--
   --#      -- After each call to UpdateDoorAlarm, the security   --
   --#      -- property holds.                                    --
   --#      --------------------------------------------------------
   --#      ( CurrentDoor = Open and
   --#        Latch.IsLocked(Latch.State) and
   --#        Clock.GreaterThanOrEqual(Clock.TheCurrentTime(Clock.CurrentTime),
   --#                                 AlarmTimeout) ) <->
   --#      DoorAlarm = AlarmTypes.Alarming;
   is
      LocalAlarm : AlarmTypes.StatusT;
      Severity   : AuditTypes.SeverityT;
      ID         : AuditTypes.ElementT;
   begin
      if CurrentDoor = Open and
            Latch.IsLocked and
            Clock.GreaterThanOrEqual(Left  => Clock.TheCurrentTime,
                                     Right => AlarmTimeout) then

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

   procedure Poll(SystemFault :    out Boolean)
   --# global in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in     Clock.CurrentTime;
   --#        in     AlarmTimeout;
   --#        in     Interface.Input;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#        in out Latch.State;
   --#        in out DoorAlarm;
   --#        in out CurrentDoor;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 Clock.CurrentTime,
   --#                                 Latch.State,
   --#                                 DoorAlarm,
   --#                                 AlarmTimeout,
   --#                                 CurrentDoor,
   --#                                 Interface.Input &
   --#         Latch.State        from *,
   --#                                 Clock.CurrentTime &
   --#         SystemFault        from Interface.Input &
   --#         DoorAlarm          from Clock.CurrentTime,
   --#                                 Latch.State,
   --#                                 AlarmTimeout,
   --#                                 CurrentDoor,
   --#                                 Interface.Input &
   --#         CurrentDoor        from *,
   --#                                 Interface.Input;
   --# post
   --#      --------------------------------------------------------
   --#      -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
   --#      --====================================================--
   --#      -- After each call to Poll, the security property     --
   --#      -- holds.                                             --
   --#      --------------------------------------------------------
   --#      ( ( CurrentDoor = Open and
   --#          Latch.IsLocked(Latch.State) and
   --#          Clock.GreaterThanOrEqual(Clock.TheCurrentTime(Clock.CurrentTime),
   --#                                   AlarmTimeout) ) <->
   --#        DoorAlarm = AlarmTypes.Alarming ) and
   --#
   --#
   --#      ( Latch.IsLocked(Latch.State) <->
   --#        Clock.GreaterThanOrEqual(Clock.TheCurrentTime(Clock.CurrentTime),
   --#                                 Latch.prf_LatchTimeout(Latch.State)) ) and
   --#      ( Latch.IsLocked(Latch.State~) ->
   --#                 (Latch.State = Latch.State~ and
   --#                  Latch.IsLocked(Latch.State) ) ) and
   --#      Latch.prf_latchTimeout(Latch.State) = Latch.prf_latchTimeout(Latch.State~);
   is
      NewDoor : T;
      ID      : AuditTypes.ElementT;
   begin
      Interface.GetDoorState(DoorState => NewDoor,
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
   --# global in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in     Clock.CurrentTime;
   --#        in     CurrentDoor;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#        in out Latch.State;
   --#        in out DoorAlarm;
   --#           out AlarmTimeout;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 Clock.CurrentTime,
   --#                                 Latch.State,
   --#                                 DoorAlarm,
   --#                                 CurrentDoor &
   --#         Latch.State        from *,
   --#                                 ConfigData.State,
   --#                                 Clock.CurrentTime &
   --#         DoorAlarm          from ConfigData.State,
   --#                                 Clock.CurrentTime,
   --#                                 Latch.State,
   --#                                 CurrentDoor &
   --#         AlarmTimeout       from ConfigData.State,
   --#                                 Clock.CurrentTime;
   --# post
   --#      --------------------------------------------------------
   --#      -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
   --#      --====================================================--
   --#      -- After each call to UnlockDoor, the security        --
   --#      -- property holds.                                    --
   --#      --------------------------------------------------------
   --#      ( ( CurrentDoor = Open and
   --#          Latch.IsLocked(Latch.State) and
   --#          Clock.GreaterThanOrEqual(Clock.TheCurrentTime(Clock.CurrentTime),
   --#                                   AlarmTimeout) ) <->
   --#        DoorAlarm = AlarmTypes.Alarming ) and
   --#
   --#      ( Latch.IsLocked(Latch.State) <->
   --#        Clock.GreaterThanOrEqual(Clock.TheCurrentTime(Clock.CurrentTime),
   --#                                 Latch.prf_LatchTimeout(Latch.State)) );
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
   --# global in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in     Clock.CurrentTime;
   --#        in     CurrentDoor;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#        in out Latch.State;
   --#        in out DoorAlarm;
   --#           out AlarmTimeout;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 Clock.CurrentTime,
   --#                                 Latch.State,
   --#                                 DoorAlarm,
   --#                                 CurrentDoor &
   --#         Latch.State        from *,
   --#                                 Clock.CurrentTime &
   --#         DoorAlarm          from Clock.CurrentTime,
   --#                                 Latch.State,
   --#                                 CurrentDoor &
   --#         AlarmTimeout       from Clock.CurrentTime;
   --# post
   --#      --------------------------------------------------------
   --#      -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
   --#      --====================================================--
   --#      -- After each call to LockDoor, the security property --
   --#      -- holds.                                             --
   --#      --------------------------------------------------------
   --#      ( ( CurrentDoor = Open and
   --#          Latch.IsLocked(Latch.State) and
   --#          Clock.GreaterThanOrEqual(Clock.TheCurrentTime(Clock.CurrentTime),
   --#                                   AlarmTimeout) ) <->
   --#        DoorAlarm = AlarmTypes.Alarming ) and
   --#      Latch.IsLocked(Latch.State);
   is
   begin

      Latch.SetTimeout(Time => Clock.TheCurrentTime);
      AlarmTimeout := Clock.TheCurrentTime;

      Latch.UpdateInternalLatch;
      --# check Latch.prf_latchTimeout(Latch.State) =
      --#         Clock.TheCurrentTime(Clock.CurrentTime);
      UpdateDoorAlarm;

      --# check Clock.GreaterThanOrEqual(Clock.TheCurrentTime(Clock.CurrentTime),
      --#                                AlarmTimeout);

   end LockDoor;



   ------------------------------------------------------------------
   -- Init
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------

   procedure Init
   --# global out DoorAlarm;
   --#        out AlarmTimeout;
   --#        out CurrentDoor;
   --# derives DoorAlarm,
   --#         AlarmTimeout,
   --#         CurrentDoor  from ;
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

   function TheCurrentDoor return T
   --# global CurrentDoor;
   is
   begin
      return CurrentDoor;
   end TheCurrentDoor;


   ------------------------------------------------------------------
   -- TheDoorAlarm
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------

   function TheDoorAlarm return AlarmTypes.StatusT
   --# global DoorAlarm;
   is
   begin
      return DoorAlarm;
   end TheDoorAlarm;


   ------------------------------------------------------------------
   -- Failure
   --
   -- Implementation notes:
   --    None
   --
   ------------------------------------------------------------------

   procedure Failure
   --# global out Latch.State;
   --#        out DoorAlarm;
   --#        out AlarmTimeout;
   --#        out CurrentDoor;
   --# derives Latch.State,
   --#         DoorAlarm,
   --#         AlarmTimeout,
   --#         CurrentDoor  from ;
   is
   begin
      CurrentDoor  := Open;
      AlarmTimeout := Clock.ZeroTime;
      DoorAlarm    := AlarmTypes.Alarming;
      Latch.Failure;
   end Failure;

end Door;
