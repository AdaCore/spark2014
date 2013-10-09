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

with Latch.Interfac,
     AuditLog,
     AuditTypes;

package body Latch
--# own State  is CurrentLatch,
--#               LatchTimeout &
--#     Output is    out Latch.Interfac.Output;
is pragma SPARK_Mode (On);

   function Latch_Timeout return Clock.TimeT is
   begin
      return LatchTimeout;
   end Latch_Timeout;

   function LatchIsLocked return Boolean is
   begin
      return Latch.Interfac.IsLocked;
   end LatchIsLocked;

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
      pragma Postcondition
        (( IsLocked =
           Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
                                    LatchTimeout) ));
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
   --#           out Interfac.Output;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 CurrentLatch &
   --#         Interfac.Output,
   --#         SystemFault        from CurrentLatch;
   --# post ( IsLocked(CurrentLatch) <->
   --#           Interfac.prf_isLocked(Interfac.Output) ) or else
   --#      SystemFault;
   is
      pragma Postcondition
        (( IsLocked =
              Interfac.isLocked ) or
         SystemFault);
   begin
      if CurrentLatch = Locked then
         Interfac.Lock(Fault => SystemFault);
      else
         Interfac.Unlock(Fault => SystemFault);
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
      pragma Postcondition (LatchTimeout = Time);
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
