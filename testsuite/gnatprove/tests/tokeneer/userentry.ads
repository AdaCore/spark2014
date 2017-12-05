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
-- UserEntry
--
-- Description:
--    Manages the user entry operation.
--
------------------------------------------------------------------
with AlarmTypes,
     AuditLog,
     AuditTypes,
     CommonTypes,
     Bio,
     CertificateStore,
     Clock,
     ConfigData,
     Display,
     Door,
     IandATypes,
     KeyStore,
     Latch,
     Stats,
     UserToken;

use AlarmTypes,
    Door;

package UserEntry
  with Abstract_State => State,
       Initializes    => State
is


   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------

   --# type Prf_StateT is abstract;

      ---------------------------------------------------------
      -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 1           --
      --=====================================================--
      -- Proof function to act as a holder for the           --
      -- annotations of the User Entry part of property 1 -  --
      -- if the door is unlocked, then either a guard is     --
      -- present, or a user entry operation is in progress.  --
      ---------------------------------------------------------
   --# function prf_UserEntryUnlockDoor return Boolean;

   -- The previous proof function, in SPARK 2014, translates into:
   --   (Latch.IsLocked'Old and
   --      not Latch.IsLocked);

   ------------------------------------------------------------------
   -- CurrentActivityPossible
   --
   -- Description:
   --    Returns true if and only if the system is in a state where
   --    it can progress a current user entry operation.
   --
   -- traceunit : C.UserEntry.CurrentActivityPossible
   -- traceto : FD.UserEntry.CurrentUserEntryActivityPossible
   ------------------------------------------------------------------
   function CurrentActivityPossible return Boolean
     with Global => (State,
                     UserToken.State);

   ------------------------------------------------------------------
   -- CanStart
   --
   -- Description:
   --    Returns true if and only if the system is in a state where
   --    it can start a new user entry operation.
   --
   -- traceunit : C.UserEntry.CanStart
   -- traceto : FD.UserEntry.UserEntryCanStart
   ------------------------------------------------------------------
   function CanStart return Boolean
     with Global => (State,
                     UserToken.State);

   ------------------------------------------------------------------
   -- InProgress
   --
   -- Description:
   --    Determines whether user entry is in progress.
   --
   -- Traceunit : C.UserEntry.InProgress
   -- Traceto : FD.UserEntry.UserEntryInProgress
   ------------------------------------------------------------------
   function InProgress return Boolean
      with Global => State;

   ------------------------------------------------------------------
   -- DisplayPollUpdate
   --
   -- Description:
   --    Progresses a user entry that has already started.
   --
   -- traceunit : C.UserEntry.DisplayPollUpdate
   -- traceto : FD.Interfac.DisplayPollUpdate
   ------------------------------------------------------------------
   procedure DisplayPollUpdate
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State,
                                 Latch.State,
                                 State),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 Display.State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Display.State,
                                               Latch.State,
                                               State),
                      Display.State        =>+ (Latch.State,
                                                State));

   ------------------------------------------------------------------
   -- Progress
   --
   -- Description:
   --    Progresses a user entry that has already started.
   --
   -- traceunit : C.UserEntry.Progress
   -- traceto : FD.UserEntry.ProgressUserEntry
   ------------------------------------------------------------------
   procedure Progress (TheStats : in out Stats.T)
     with Global  => (Input  => (Bio.Input,
                                 Clock.CurrentTime,
                                 Clock.Now,
                                 ConfigData.State,
                                 KeyStore.State,
                                 KeyStore.Store,
                                 UserToken.Input),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 CertificateStore.FileState,
                                 CertificateStore.State,
                                 Display.State,
                                 Door.State,
                                 Latch.State,
                                 State,
                                 UserToken.Output,
                                 UserToken.State,
                                 UserToken.Status)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State) => (AuditLog.FileState,
                                           AuditLog.State,
                                           Bio.Input,
                                           CertificateStore.FileState,
                                           CertificateStore.State,
                                           Clock.CurrentTime,
                                           Clock.Now,
                                           ConfigData.State,
                                           Display.State,
                                           Door.State,
                                           KeyStore.State,
                                           KeyStore.Store,
                                           Latch.State,
                                           State,
                                           UserToken.Input,
                                           UserToken.State,
                                           UserToken.Status),

                      (CertificateStore.FileState,
                       CertificateStore.State) =>+ (CertificateStore.State,
                                                    Clock.CurrentTime,
                                                    ConfigData.State,
                                                    KeyStore.State,
                                                    KeyStore.Store,
                                                    State,
                                                    UserToken.State,
                                                    UserToken.Status),

                      Display.State =>+ (Bio.Input,
                                         CertificateStore.State,
                                         Clock.CurrentTime,
                                         ConfigData.State,
                                         KeyStore.State,
                                         KeyStore.Store,
                                         State,
                                         UserToken.Input,
                                         UserToken.State,
                                         UserToken.Status),

                      (Door.State,
                       Latch.State) =>+ (Clock.CurrentTime,
                                         ConfigData.State,
                                         Latch.State,
                                         State,
                                         UserToken.State),

                      State =>+ (Bio.Input,
                                 Clock.CurrentTime,
                                 ConfigData.State,
                                 KeyStore.State,
                                 KeyStore.Store,
                                 UserToken.Input,
                                 UserToken.State,
                                 UserToken.Status),

                      TheStats =>+ (Bio.Input,
                                    ConfigData.State,
                                    State,
                                    UserToken.State),

                      UserToken.Output =>+ (CertificateStore.State,
                                            Clock.CurrentTime,
                                            ConfigData.State,
                                            KeyStore.State,
                                            KeyStore.Store,
                                            State,
                                            UserToken.State,
                                            UserToken.Status),

                      (UserToken.State,
                       UserToken.Status) => (CertificateStore.State,
                                             Clock.CurrentTime,
                                             ConfigData.State,
                                             KeyStore.State,
                                             KeyStore.Store,
                                             State,
                                             UserToken.Input,
                                             UserToken.State,
                                             UserToken.Status)),


          Pre     =>
            CurrentActivityPossible and
            KeyStore.PrivateKeyPresent and

            --------------------------------------------------------
            -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
            --====================================================--
            -- Before each call to Progress, the security         --
            -- property holds.                                    --
            --------------------------------------------------------
            (((Latch.IsLocked and
                 Door.TheCurrentDoor = Door.Open and
                 Clock.GreaterThanOrEqual (Clock.TheCurrentTime,
                                           Door.Alarm_TimeOut)))
             = (Door.TheDoorAlarm = AlarmTypes.Alarming)),
          Post    =>
            --------------------------------------------------------
            -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
            --====================================================--
            -- After each call to Progress, the security property --
            -- holds.                                             --
            --------------------------------------------------------
            (((Latch.IsLocked and
                 Door.TheCurrentDoor = Door.Open and
                 Clock.GreaterThanOrEqual (Clock.TheCurrentTime,
                                           Door.Alarm_Timeout)))
             = (Door.TheDoorAlarm = AlarmTypes.Alarming));









   ------------------------------------------------------------------
   -- StartEntry
   --
   -- Description:
   --    Starts a new user entry operation.
   --
   -- traceunit : C.UserEntry.StartEntry
   -- traceto : FD.UserEntry.TISReadUserToken
   ------------------------------------------------------------------
   procedure StartEntry
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 Display.State,
                                 State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Display.State),
                      (Display.State,
                       State)               =>+ null);

end UserEntry;
