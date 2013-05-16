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
-- Latch
--
-- Description:
--    Provides interface to the portal latch
--
------------------------------------------------------------------

with Clock;
--# inherit AuditLog,
--#         AuditTypes,
--#         Clock,
--#         ConfigData;

package Latch
--# own State : StateType;
--#     out Output : OutType;
is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   --# type StateType is Abstract;
   --# type OutType is Abstract;
   --# function prf_isLocked(Output : OutType) return Boolean;
   --# function prf_latchTimeout(State : StateType) return Clock.TimeT;

   ------------------------------------------------------------------
   -- Init
   --
   -- Description:
   --    Initializes State
   --
   -- Traceunit : C.Latch.Init
   -- Traceto   : FD.TIS.InitIDStation
   ------------------------------------------------------------------

   procedure Init;
   --# global out State;
   --# derives State from ;


   ------------------------------------------------------------------
   -- IsLocked
   --
   -- Implementation Notes:
   --    Returns to the caller whether the internal view of the latch
   --    is 'locked' or not.
   --
   -- Traceunit : C.Latch.IsLocked
   -- Traceto   : FD.RealWorld.State
   ------------------------------------------------------------------
   function IsLocked return Boolean;
   --# global State;


   ------------------------------------------------------------------
   -- UpdateInternalLatch
   --
   -- Description:
   --    Updates the internal view of the latch depending on whether the
   --    latch timeout has passed.
   --
   -- Traceunit : C.Latch.UpdateInternalLatch
   -- Traceto   : FD.Latch.UpdateInternalLatch
   ------------------------------------------------------------------

   procedure UpdateInternalLatch;
   --# global in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in     Clock.CurrentTime;
   --#        in out State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from State,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 Clock.CurrentTime &
   --#         State              from *,
   --#                                 Clock.CurrentTime;
   --# post ( IsLocked(State) <->
   --#        Clock.GreaterThanOrEqual(Clock.TheCurrentTime(Clock.CurrentTime),
   --#                                 prf_LatchTimeout(State)) ) and
   --#      prf_latchTimeout(State) = prf_latchTimeout(State~);



   ------------------------------------------------------------------
   -- UpdateDevice
   --
   -- Description:
   --    Sets the physical latch to match the internal latch.
   --    May raise a system fault.
   --
   -- Traceunit : C.Latch.UpdateDevice
   -- Traceto   : FD.Interface.UpdateLatch
   ------------------------------------------------------------------

   procedure UpdateDevice(SystemFault :    out Boolean);
   --# global in     State;
   --#        in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#           out Output;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from State,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Clock.Now,
   --#                                 ConfigData.State &
   --#         Output,
   --#         SystemFault        from State;
   --# post ( IsLocked(State) <-> prf_isLocked(Output) )
   --#      or SystemFault;


   ------------------------------------------------------------------
   -- SetTimeout
   --
   -- Description:
   --    Updates the latch timeout
   --
   -- Traceunit : C.Latch.SetTimeout
   -- Traceto   : FD.Door.UnlockDoor
   --             FD.Door.LockDoor
   ------------------------------------------------------------------

   procedure SetTimeout(Time : Clock.TimeT);
   --# global in out State;
   --# derives State from *,
   --#                    Time;
   --# post prf_latchTimeout(State) = Time;


   ------------------------------------------------------------------
   -- Failure
   --
   -- Description:
   --    Sets state to make system as secure as possible following a
   --    critical system Door/Latch fault
   --
   -- Traceunit : C.Latch.Failure
   --
   ------------------------------------------------------------------
   procedure Failure;
   --# global out State;
   --# derives State from ;

end Latch;
