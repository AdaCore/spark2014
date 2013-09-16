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
-- Door
--
-- Description:
--    Provides interface to the portal door.
--
------------------------------------------------------------------
with AlarmTypes;
--# inherit AlarmTypes,
--#         AuditLog,
--#         AuditTypes,
--#         Clock,
--#         ConfigData,
--#         Latch;
with Clock;
with Latch; use Latch;
use AlarmTypes;
use Clock;

package Door
--# own State : StateType;
--#     in Input;
is pragma SPARK_Mode (On);

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   type T is (Open, Closed);


   ---------------------------------------------------------
   -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3           --
   --=====================================================--
   -- A proof function is required to model the Alarm     --
   -- Timeout (which is not visible outside the package   --
   -- body).                                              --
   -- AlarmTimeout is a component of Door.State, so need  --
   -- to take Door.State as a parameter of the function   --
   -- To do this, need to define an abstract type for     --
   -- Door.State.                                         --
   ---------------------------------------------------------
   --# type StateType is Abstract;
   --#
   --# function prf_alarmTimeout(DoorState : StateType)
   --#    return Clock.TimeT;
   function Alarm_Timeout return Clock.TimeT;

   ------------------------------------------------------------------
   -- TheCurrentDoor
   --
   -- Description:
   --    Returns the current state of the door.
   --
   -- Traceunit : C.Door.TheCurrentDoor
   -- Traceto   : FD.RealWorld.State
   ------------------------------------------------------------------

   function TheCurrentDoor return T;
   --# global State;


   ------------------------------------------------------------------
   -- TheDoorAlarm
   --
   -- Description:
   --    Returns the current state of the alarm.
   --
   -- Traceunit : C.Door.TheDoorAlarm
   -- Traceto   : FD.RealWorld.State
   ------------------------------------------------------------------

   function TheDoorAlarm return AlarmTypes.StatusT;
   --# global State;


   ------------------------------------------------------------------
   -- Poll
   --
   -- Description:
   --    Polls the door, and updates the door alarm and latch alarm
   --    appropriately. Audit Log may be updated.
   --
   -- Traceunit : C.Door.Poll
   -- Traceto: FD.Interfac.PollDoor
   --          FD.Interfac.TISPoll
   --
   ------------------------------------------------------------------

   procedure Poll(SystemFault :    out Boolean);
   --# global in     Input;
   --#        in     Clock.CurrentTime;
   --#        in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out State;
   --#        in out Latch.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from State,
   --#                                 Input,
   --#                                 Clock.CurrentTime,
   --#                                 Latch.State,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Clock.Now,
   --#                                 ConfigData.State &
   --#         State              from *,
   --#                                 Input,
   --#                                 Clock.CurrentTime,
   --#                                 Latch.State &
   --#         Latch.State        from *,
   --#                                 Clock.CurrentTime &
   --#         SystemFault        from Input;
   --# post
   --#      --------------------------------------------------------
   --#      -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
   --#      --====================================================--
   --#      -- After each call to Poll, the security property     --
   --#      -- holds.                                             --
   --#      --------------------------------------------------------
   --#      ( ( Latch.IsLocked(Latch.State) and
   --#          TheCurrentDoor(State) = Open and
   --#          Clock.GreaterThanOrEqual(Clock.TheCurrentTime(Clock.CurrentTime),
   --#                                   prf_alarmTimeout(State)) ) <->
   --#        TheDoorAlarm(State) = AlarmTypes.Alarming ) and
   --#
   --#
   --#
   --#      ( Latch.IsLocked(Latch.State) <->
   --#        Clock.GreaterThanOrEqual(Clock.TheCurrentTime(Clock.CurrentTime),
   --#                                 Latch.prf_LatchTimeout(Latch.State)) ) and
   --#      ( Latch.IsLocked(Latch.State~) ->
   --#                ( Latch.State = Latch.State~ and
   --#                  Latch.IsLocked(Latch.State) ) ) and
   --#      Latch.prf_latchTimeout(Latch.State) = Latch.prf_latchTimeout(Latch.State~);
   pragma Postcondition
     ( ( Latch.IsLocked and
      TheCurrentDoor = Open and
      Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
        Alarm_Timeout) ) =
      (TheDoorAlarm = AlarmTypes.Alarming ) and

        ( Latch.IsLocked =
           Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
             Latch.Latch_Timeout) ) and
         ( Latch.IsLocked'Old <=
           ( Latch.CurrentLatch = Latch.CurrentLatch'Old and
            Latch.LatchTimeout = Latch.LatchTimeout'Old and
            Latch.IsLocked ) ) and
      Latch.Latch_Timeout = Latch.Latch_Timeout'Old);


   ------------------------------------------------------------------
   -- UnlockDoor
   --
   -- Description:
   --    Unlocks the door, and sets the latch timeout and alarm timeout.
   --    Audit Log may be updated.
   --
   -- traceunit : C.Door.UnlockDoor
   -- traceto   : FD.Door.UnlockDoor
   ------------------------------------------------------------------

   procedure UnlockDoor;
   --# global in     Clock.CurrentTime;
   --#        in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out State;
   --#        in out Latch.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --# derives State,
   --#         Latch.State        from *,
   --#                                 Clock.CurrentTime,
   --#                                 Latch.State,
   --#                                 ConfigData.State &
   --#         AuditLog.State,
   --#         AuditLog.FileState from State,
   --#                                 Clock.CurrentTime,
   --#                                 Latch.State,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Clock.Now,
   --#                                 ConfigData.State;
   --# post
   --#      --------------------------------------------------------
   --#      -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
   --#      --====================================================--
   --#      -- After each call to UnlockDoor, the security        --
   --#      -- property holds.                                    --
   --#      --------------------------------------------------------
   --#      ( ( Latch.IsLocked(Latch.State) and
   --#          TheCurrentDoor(State) = Open and
   --#          Clock.GreaterThanOrEqual(Clock.TheCurrentTime(Clock.CurrentTime),
   --#                                   prf_alarmTimeout(State)) ) <->
   --#        TheDoorAlarm(State) = AlarmTypes.Alarming ) and
   --#
   --#
   --#      ( Latch.IsLocked(Latch.State) <->
   --#        Clock.GreaterThanOrEqual(Clock.TheCurrentTime(Clock.CurrentTime),
   --#                                 Latch.prf_LatchTimeout(Latch.State)) );
   --#
   pragma Postcondition
     ( ( Latch.IsLocked and then
      TheCurrentDoor = Open and then
      Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
        Alarm_Timeout) ) =
           (TheDoorAlarm = AlarmTypes.Alarming ) and then

        ( Latch.IsLocked =
           Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
                                    Latch.Latch_Timeout) ));

   ------------------------------------------------------------------
   -- LockDoor
   --
   -- Description:
   --    Locks the door, and resets the latch timeout and alarm timeout.
   --    Audit Log may be updated.
   --
   -- traceunit : C.Door.LockDoor
   -- traceto   : FD.Door.LockDoor
   ------------------------------------------------------------------

   procedure LockDoor;
   --# global in     Clock.CurrentTime;
   --#        in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out State;
   --#        in out Latch.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --# derives State,
   --#         Latch.State        from *,
   --#                                 Clock.CurrentTime,
   --#                                 Latch.State &
   --#         AuditLog.State,
   --#         AuditLog.FileState from State,
   --#                                 Clock.CurrentTime,
   --#                                 Latch.State,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Clock.Now,
   --#                                 ConfigData.State;
   --# post
   --#      --------------------------------------------------------
   --#      -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
   --#      --====================================================--
   --#      -- After each call to LockDoor, the security property --
   --#      -- holds.                                             --
   --#      --------------------------------------------------------
   --#      ( ( Latch.IsLocked(Latch.State) and
   --#          TheCurrentDoor(State) = Open and
   --#          Clock.GreaterThanOrEqual(Clock.TheCurrentTime(Clock.CurrentTime),
   --#                                   prf_alarmTimeout(State)) ) <->
   --#        TheDoorAlarm(State) = AlarmTypes.Alarming ) and
   --#      Latch.IsLocked(Latch.State);
   pragma Postcondition
     ( ( Latch.IsLocked and then
      TheCurrentDoor = Open and then
      Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
        Alarm_Timeout) ) =
      (TheDoorAlarm = AlarmTypes.Alarming ) and then
      Latch.IsLocked);

   ------------------------------------------------------------------
   -- Init
   --
   -- Description:
   --    Initializes door state to closed and locked, and the alarm
   --    timeout to zero time.
   --
   -- Traceunit : C.Door.Init
   -- Traceto   : FD.TIS.InitIDStation
   --             FD.TIS.TISStartUp
   ------------------------------------------------------------------

   procedure Init;
   --# global out State;
   --# derives State from ;


   ------------------------------------------------------------------
   -- Failure
   --
   -- Description:
   --    Sets state to make system as secure as possible following a
   --    critical system Door/Latch fault
   --
   -- Traceunit : C.Door.Failure
   --
   ------------------------------------------------------------------
   procedure Failure;
   --# global out State;
   --#        out Latch.State;
   --# derives State,
   --#         Latch.State from ;

end Door;
