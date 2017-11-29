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
-- Description:
--    Provides interface to the portal door.
--
------------------------------------------------------------------
with AlarmTypes;  use AlarmTypes;
with AuditLog;
with Clock;       use Clock;
with ConfigData;
with Latch;       use Latch;

package Door
  with Abstract_State => (State,
                          (Input with External => Async_Writers))
is

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
   function Alarm_Timeout return Clock.TimeT
     with Global     => State,
          Ghost;

   ------------------------------------------------------------------
   -- TheCurrentDoor
   --
   -- Description:
   --    Returns the current state of the door.
   --
   -- Traceunit : C.Door.TheCurrentDoor
   -- Traceto   : FD.RealWorld.State
   ------------------------------------------------------------------
   function TheCurrentDoor return T
     with Global => State;

   ------------------------------------------------------------------
   -- TheDoorAlarm
   --
   -- Description:
   --    Returns the current state of the alarm.
   --
   -- Traceunit : C.Door.TheDoorAlarm
   -- Traceto   : FD.RealWorld.State
   ------------------------------------------------------------------
   function TheDoorAlarm return AlarmTypes.StatusT
     with Global => State;

   ------------------------------------------------------------------
   -- Poll
   --
   -- Description:
   --    Polls the door, and updates the door alarm and latch alarm
   --    appropriately.Audit Log may be updated.
   --
   -- Traceunit : C.Door.Poll
   -- Traceto: FD.Interfac.PollDoor
   --          FD.Interfac.TISPoll
   --
   ------------------------------------------------------------------
   procedure Poll (SystemFault :    out Boolean)
     with Global  => (Input  => (Clock.CurrentTime,
                                 Clock.Now,
                                 ConfigData.State,
                                 Input),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 Latch.State,
                                 State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.CurrentTime,
                                               Clock.Now,
                                               ConfigData.State,
                                               Input,
                                               Latch.State,
                                               State),
                      Latch.State          =>+ Clock.CurrentTime,
                      State                =>+ (Clock.CurrentTime,
                                                Input,
                                                Latch.State),
                      SystemFault          => Input),
          --------------------------------------------------------
          -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
          --====================================================--
          -- After each call to Poll, the security property     --
          -- holds.                                             --
          --------------------------------------------------------
          Post    => (Latch.IsLocked and
                      TheCurrentDoor = Open and
                      Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
                                               Alarm_Timeout)) =
                        (TheDoorAlarm = AlarmTypes.Alarming) and

                      Latch.IsLocked =
                        Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
                                                 Latch.Latch_Timeout) and

                     Latch.Latch_Timeout = Latch.Latch_Timeout'Old;

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
   procedure UnlockDoor
     with Global  => (Input  => (Clock.CurrentTime,
                                 Clock.Now,
                                 ConfigData.State),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 Latch.State,
                                 State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.CurrentTime,
                                               Clock.Now,
                                               ConfigData.State,
                                               Latch.State,
                                               State),
                      (Latch.State,
                       State)              =>+ (Clock.CurrentTime,
                                                ConfigData.State,
                                                Latch.State)),
          --------------------------------------------------------
          -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
          --====================================================--
          -- After each call to UnlockDoor, the security        --
          -- property holds.                                    --
          --------------------------------------------------------
          Post    => (Latch.IsLocked and
                      TheCurrentDoor = Open and
                      Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
                                               Alarm_Timeout)) =
                        (TheDoorAlarm = AlarmTypes.Alarming) and
                     Latch.IsLocked =
                       Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
                                                Latch.Latch_Timeout);

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
   procedure LockDoor
     with Global  => (Input  => (Clock.CurrentTime,
                                 Clock.Now,
                                 ConfigData.State),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 Latch.State,
                                 State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.CurrentTime,
                                               Clock.Now,
                                               ConfigData.State,
                                               Latch.State,
                                               State),
                      (Latch.State,
                       State)              =>+ (Clock.CurrentTime,
                                                Latch.State)),
          --------------------------------------------------------
          -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
          --====================================================--
          -- After each call to LockDoor, the security property --
          -- holds.                                             --
          --------------------------------------------------------
          Post    => (Latch.IsLocked and
                      TheCurrentDoor = Open and
                      Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
                                               Alarm_Timeout)) =
                        (TheDoorAlarm = AlarmTypes.Alarming) and
                        Latch.IsLocked;

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
   procedure Init
     with Global  => (Output => State),
          Depends => (State => null);

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
   procedure Failure
     with Global  => (Output => (Latch.State,
                                 State)),
          Depends => ((Latch.State,
                       State) => null);

end Door;
