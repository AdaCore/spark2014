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
-- Implementation Notes:
--    None
--
------------------------------------------------------------------

with Latch.Interface,
     AuditLog,
     AuditTypes;

package body Latch
--# own State  is CurrentLatch,
--#               LatchTimeout &
--#     Output is    out Latch.Interface.Output;
is


   type T is (Locked, Unlocked);
   CurrentLatch : T;
   LatchTimeout : Clock.TimeT;


   ------------------------------------------------------------------
   -- Init
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------

   procedure Init
   --# global out CurrentLatch;
   --#        out LatchTimeout;
   --# derives CurrentLatch,
   --#         LatchTimeout from ;
   is
   begin
      CurrentLatch := Locked;
      LatchTimeout := Clock.ZeroTime;
   end Init;


   ------------------------------------------------------------------
   -- IsLocked
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   function IsLocked return Boolean
   --# global CurrentLatch;
   is
   begin
      return CurrentLatch = Locked;
   end IsLocked;


   ------------------------------------------------------------------
   -- UpdateInternalLatch
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------

   procedure UpdateInternalLatch
   --# global in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in     Clock.CurrentTime;
   --#        in     LatchTimeout;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#        in out CurrentLatch;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 Clock.CurrentTime,
   --#                                 CurrentLatch,
   --#                                 LatchTimeout &
   --#         CurrentLatch       from Clock.CurrentTime,
   --#                                 LatchTimeout;
   --# post ( IsLocked(CurrentLatch) <->
   --#        Clock.GreaterThanOrEqual(Clock.TheCurrentTime(Clock.CurrentTime),
   --#                                 LatchTimeout) );
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
                ElementID    => ID,
                Severity     => AuditTypes.Information,
                User         => AuditTypes.NoUser,
                Description  => AuditTypes.NoDescription
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

   procedure UpdateDevice(SystemFault :    out Boolean)
   --# global in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in     CurrentLatch;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#           out Interface.Output;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 CurrentLatch &
   --#         Interface.Output,
   --#         SystemFault        from CurrentLatch;
   --# post ( IsLocked(CurrentLatch) <->
   --#           Interface.prf_isLocked(Interface.Output) ) or
   --#      SystemFault;
   is
   begin
      if CurrentLatch = Locked then
         Interface.Lock(Fault => SystemFault);
      else
         Interface.Unlock(Fault => SystemFault);
      end if;

      if SystemFault then
         -- Door is in error state - raise a critical system fault
         AuditLog.AddElementToLog(
                ElementID    => AuditTypes.SystemFault,
                Severity     => AuditTypes.Critical,
                User         => AuditTypes.NoUser,
                Description  => "LATCH STATE CANNOT BE DETERMINED."
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

   procedure SetTimeout(Time : Clock.TimeT)
   --# global out LatchTimeout;
   --# derives LatchTimeout from Time;
   --# post LatchTimeout = Time;
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
   --# global out CurrentLatch;
   --#        out LatchTimeout;
   --# derives CurrentLatch,
   --#         LatchTimeout from ;
   is
   begin
      CurrentLatch := Locked;
      LatchTimeout := Clock.ZeroTime;
   end Failure;

end Latch;
