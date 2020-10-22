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
-- Latch
--
-- Description:
--    Provides interface to the portal latch
--
------------------------------------------------------------------

with AuditLog,
     ConfigData,
     Clock;

use Clock;

package Latch
  with SPARK_Mode,
       Abstract_State => (State,
                          (Output with External => Async_Readers)),
       Initializes => Output
is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   type T is (Locked, Unlocked);

   --  Proof functions (ghost functions)
   function Current_Latch return T
     with Global     => State,
          Ghost;

   function Latch_Timeout return Clock.TimeT
     with Global     => State,
          Ghost;

   function LatchIsLocked return Boolean
     with Global     => null,
          Ghost;

   ------------------------------------------------------------------
   -- Init
   --
   -- Description:
   --    Initializes State
   --
   -- Traceunit : C.Latch.Init
   -- Traceto   : FD.TIS.InitIDStation
   ------------------------------------------------------------------
   procedure Init
     with Global  => (Output => State),
          Depends => (State => null);

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
   function IsLocked return Boolean
     with Global => State;

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
   procedure UpdateInternalLatch
     with Global  => (Input  => (Clock.CurrentTime,
                                 Clock.Now,
                                 ConfigData.State),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.CurrentTime,
                                               Clock.Now,
                                               ConfigData.State,
                                               State),
                      State                =>+ Clock.CurrentTime),
          Post    => IsLocked = Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
                                                         Latch_Timeout) and
                     Latch_Timeout = Latch_Timeout'Old;

   ------------------------------------------------------------------
   -- UpdateDevice
   --
   -- Description:
   --    Sets the physical latch to match the internal latch.
   --    May raise a system fault.
   --
   -- Traceunit : C.Latch.UpdateDevice
   -- Traceto   : FD.Interfac.UpdateLatch
   ------------------------------------------------------------------
   procedure UpdateDevice (SystemFault :    out Boolean)
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State,
                                 State),
                      Output => Output,
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               State),
                      (Output,
                       SystemFault)        => State),
          Post    => (IsLocked = LatchisLocked) or SystemFault;

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
   procedure SetTimeout (Time : Clock.TimeT)
     with Global  => (In_Out => State),
          Depends => (State =>+ Time),
          Post    => Latch_Timeout = Time;

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
   procedure Failure
     with Global  => (Output => State),
          Depends => (State => null);

private
   CurrentLatch : T with Part_Of => State;
   LatchTimeout : Clock.TimeT with Part_Of => State;

   --  Proof functions (ghost functions)
   function Current_Latch return T is (CurrentLatch)
     with Refined_Global => CurrentLatch;

   function Latch_Timeout return Clock.TimeT is (LatchTimeout)
     with Refined_Global => LatchTimeout;

   ------------------------------------------------------------------
   -- IsLocked
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   function IsLocked return Boolean is (CurrentLatch = Locked)
     with Refined_Global => CurrentLatch;

end Latch;
