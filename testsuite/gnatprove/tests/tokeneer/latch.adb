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
-- Implementation Notes:
--    None
--
------------------------------------------------------------------

with Latch.Interfac,
     AuditLog,
     AuditTypes;

package body Latch
  with Refined_State => (State  => (CurrentLatch,
                                    LatchTimeout),
                         Output => Latch.Interfac.Output)
is
   function LatchIsLocked return Boolean is (Latch.Interfac.IsLocked);

   ------------------------------------------------------------------
   -- Init
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure Init
     with Refined_Global  => (Output => (CurrentLatch,
                                         LatchTimeout)),
          Refined_Depends => ((CurrentLatch,
                               LatchTimeout) => null)
   is
   begin
      CurrentLatch := Locked;
      LatchTimeout := Clock.ZeroTime;
   end Init;

   ------------------------------------------------------------------
   -- UpdateInternalLatch
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure UpdateInternalLatch
     with Refined_Global  => (Input  => (Clock.CurrentTime,
                                         Clock.Now,
                                         ConfigData.State,
                                         LatchTimeout),
                              In_Out => (AuditLog.FileState,
                                         AuditLog.State,
                                         CurrentLatch)),
          Refined_Depends => ((AuditLog.FileState,
                               AuditLog.State)     => (AuditLog.FileState,
                                                       AuditLog.State,
                                                       Clock.CurrentTime,
                                                       Clock.Now,
                                                       ConfigData.State,
                                                       CurrentLatch,
                                                       LatchTimeout),
                              CurrentLatch         => (Clock.CurrentTime,
                                                       LatchTimeout)),
          Refined_Post    => IsLocked = Clock.GreaterThanOrEqual
                                          (Clock.TheCurrentTime,
                                           LatchTimeout)
   is
      LocalLatch : T;
      ID         : AuditTypes.ElementT;
   begin
      if Clock.GreaterThanOrEqual(Left  => Clock.TheCurrentTime,
                                  Right => LatchTimeout) then
         LocalLatch := Locked;
         ID         := AuditTypes.LatchLocked;
      else
         LocalLatch := Unlocked;
         ID         := AuditTypes.LatchUnlocked;
      end if;

      if CurrentLatch /= LocalLatch then
         AuditLog.AddElementToLog(
                ElementID   => ID,
                Severity    => AuditTypes.Information,
                User        => AuditTypes.NoUser,
                Description => AuditTypes.NoDescription
                );
      end if;

      CurrentLatch := LocalLatch;

   end UpdateInternalLatch;

   ------------------------------------------------------------------
   -- UpdateDevice
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure UpdateDevice (SystemFault :    out Boolean)
     with Refined_Global  => (Input  => (Clock.Now,
                                         ConfigData.State,
                                         CurrentLatch),
                              Output => Interfac.Output,
                              In_Out => (AuditLog.FileState,
                                         AuditLog.State)),
          Refined_Depends => ((AuditLog.FileState,
                               AuditLog.State)     => (AuditLog.FileState,
                                                       AuditLog.State,
                                                       Clock.Now,
                                                       ConfigData.State,
                                                       CurrentLatch),
                              (Interfac.Output,
                               SystemFault)        => CurrentLatch),
          Refined_Post    => IsLocked = Interfac.isLocked or SystemFault
   is
   begin
      if CurrentLatch = Locked then
         Interfac.Lock(Fault => SystemFault);
      else
         Interfac.Unlock(Fault => SystemFault);
      end if;

      if SystemFault then
         -- Door is in error state - raise a critical system fault
         AuditLog.AddElementToLog(
                ElementID   => AuditTypes.SystemFault,
                Severity    => AuditTypes.Critical,
                User        => AuditTypes.NoUser,
                Description => "LATCH STATE CANNOT BE DETERMINED."
                );
      end if;

   end UpdateDevice;

   ------------------------------------------------------------------
   -- SetTimeout
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure SetTimeout (Time : Clock.TimeT)
     with Refined_Global  => (Output => LatchTimeout),
          Refined_Depends => (LatchTimeout => Time),
          Refined_Post    => LatchTimeout = Time
   is
   begin
      LatchTimeout := Time;
   end SetTimeout;

   ------------------------------------------------------------------
   -- Failure
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure Failure
     with Refined_Global  => (Output => (CurrentLatch,
                                         LatchTimeout)),
          Refined_Depends => ((CurrentLatch,
                               LatchTimeout) => null)
   is
   begin
      CurrentLatch := Locked;
      LatchTimeout := Clock.ZeroTime;
   end Failure;

end Latch;
