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
-- Enclave
--
-- Description:
--    Manages the enclave entries.
--
------------------------------------------------------------------
with Admin,
     AdminToken,
     AuditLog,
     AuditTypes,
     AlarmTypes,
     CommonTypes,
     Clock,
     ConfigData,
     Configuration,
     Door,
     Display,
     Enrolment,
     File,
     Floppy,
     KeyStore,
     Keyboard,
     Latch,
     PrivTypes,
     Screen,
     UserToken;

use Admin,
    AdminToken,
    AlarmTypes,
    Clock,
    Door,
    Latch,
    PrivTypes;

package Enclave
  with Abstract_State => State
is
   type StatusT is (NotEnrolled,
                    WaitingEnrol,
                    WaitingEndEnrol,
                    EnclaveQuiescent,
                    WaitingRemoveAdminTokenFail,
                    GotAdminToken,
                    WaitingStartAdminOp,
                    WaitingFinishAdminOp,
                    ShutDown);

   --  Proof functions
   function GetStatus return StatusT
     with Global     => State,
          Ghost;

   function statusIsGotAdminToken return Boolean
     with Global     => State,
          Ghost;

   function statusIsWaitingRemoveAdminTokenFail return Boolean
     with Global     => State,
          Ghost;

   function statusIsWaitingStartAdminOp return Boolean
     with Global     => State,
          Ghost;

   function statusIsWaitingFinishAdminOp return Boolean
     with Global     => State,
          Ghost;

   function statusIsEnclaveQuiescent return Boolean
     with Global     => State,
          Ghost;

   function statusIsShutdown return Boolean
     with Global     => State,
          Ghost;

   ------------------------------------------------------------------
   -- EnrolmentIsInProgress
   --
   -- Description:
   --    Returns true if and only if the system currently performing
   --    an enrolment or waiting for an enrolemnt to occur.
   --
   -- traceunit : C.Enclave.EnrolmentIsInProgress
   -- traceto :
   ------------------------------------------------------------------
   function EnrolmentIsInProgress return Boolean
     with Global => State;

   ------------------------------------------------------------------
   -- Init
   --
   -- Description:
   --    Initialises the Enclave State. This requires interrogation
   --    of the KeyStore to determine whether the system is enrolled.
   --
   -- traceunit : C.Enclave.Init
   -- traceto   : FD.TIS.TISStartup
   ------------------------------------------------------------------
   procedure Init
     with Global  => (Input  => KeyStore.State,
                      Output => State),
          Depends => (State => KeyStore.State),
          Post    => (KeyStore.PrivateKeyPresent = not EnrolmentIsInProgress)
                        and (EnrolmentIsInProgress
                               or statusIsEnclaveQuiescent);

   ------------------------------------------------------------------
   -- AdminMustLogout
   --
   -- Description:
   --    Returns true if and only if the administrator needs
   --    to be logged out.
   --
   -- traceunit : C.Enclave.AdminMustLogout
   -- traceto : FD.Enclave.AdminMustLogout
   ------------------------------------------------------------------
   function AdminMustLogout (TheAdmin : Admin.T) return Boolean
     with Global => (AdminToken.State,
                     Clock.CurrentTime,
                     State);

   ------------------------------------------------------------------
   -- CurrentAdminActivityPossible
   --
   -- Description:
   --    Returns true if and only if the system is in a state where
   --    it can progress a current admin operation.
   --
   -- traceunit : C.Enclave.CurrentAdminActivityPossible
   -- traceto : FD.Enclave.CurrentAdminActivityPossible
   ------------------------------------------------------------------
   function CurrentAdminActivityPossible return Boolean
     with Global => (AdminToken.State,
                     State);

   ------------------------------------------------------------------
   -- HasShutdown
   --
   -- Description:
   --    Returns true if and only if the system is in a shutdown state.
   --
   -- traceunit : C.Enclave.HasShutdown
   -- traceto :
   ------------------------------------------------------------------
   function HasShutdown return Boolean
     with Global => State;

   ------------------------------------------------------------------
   -- EnrolOp
   --
   -- Description:
   --    Progresses enrolment.
   --
   -- Traceunit : C.Enclave.EnrolOp
   -- Traceto : FD.Enclave.TISEnrolOp
   -- Traceto : FD.Enclave.RequestEnrolment
   -- Traceto : FD.Enclave.ReadEnrolmentFloppy
   -- Traceto : FD.Enclave.ValidateEnrolmentDataOK
   -- Traceto : FD.Enclave.ValidateEnrolmentDataFail
   -- Traceto : FD.Enclave.FailedEnrolFolppyRemoved
   -- Traceto : FD.Enclave.WaitingFloppyRemoval
   ------------------------------------------------------------------
   procedure EnrolOp
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State,
                                 Floppy.Input),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 Display.State,
                                 Floppy.State,
                                 KeyStore.State,
                                 KeyStore.Store,
                                 Screen.State,
                                 State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Display.State,
                                               Floppy.State,
                                               KeyStore.Store,
                                               Screen.State,
                                               State),
                      (Display.State,
                       KeyStore.State,
                       KeyStore.Store,
                       Screen.State,
                       State)              =>+ (Floppy.State,
                                                KeyStore.Store,
                                                State),
                      Floppy.State         =>+ (Floppy.Input,
                                                State)),
          Pre     => EnrolmentIsInProgress and
                       not KeyStore.PrivateKeyPresent,
          Post    => (KeyStore.PrivateKeyPresent = not EnrolmentIsInProgress)
                       and (EnrolmentIsInProgress or
                              statusIsEnclaveQuiescent);

   ------------------------------------------------------------------
   -- AdminLogout
   --
   -- Description:
   --    Logs out an administrator.
   --
   -- Traceunit : C.Enclave.AdminLogout
   -- Traceto : FD.Enclave.TISAdminLogout
   -- Traceto : FD.Enclave.AdminLogout
   -- Traceto : FD.Enclave.BadAdminLogout
   -- Traceto : FD.Enclave.AdminTokenTimeout
   ------------------------------------------------------------------
   procedure AdminLogout (TheAdmin : in out Admin.T)
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State),
                      In_Out => (AdminToken.State,
                                 AuditLog.FileState,
                                 AuditLog.State,
                                 State)),
          Depends => ((AdminToken.State,
                       State)              => (AdminToken.State,
                                               State,
                                               TheAdmin),
                      (AuditLog.FileState,
                       AuditLog.State)     => (AdminToken.State,
                                               AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               State,
                                               TheAdmin),
                      TheAdmin             => null),
          Pre     => not EnrolmentIsInProgress
                     and (if (statusIsWaitingStartAdminOp or
                                statusIsWaitingFinishAdminOp)
                          then
                              (Admin.IsDoingOp(TheAdmin) and
                                 Admin.IsPresent(TheAdmin))),
          Post    => not EnrolmentIsInProgress
                     and Admin.RolePresent(TheAdmin) =
                           PrivTypes.UserOnly
                     and not Admin.IsDoingOp(TheAdmin)
                     and (statusIsEnclaveQuiescent or
                            statusIsWaitingRemoveAdminTokenFail or
                            GetStatus = GetStatus'Old)
                     and not (statusIsWaitingStartAdminOp or
                                statusIsWaitingFinishAdminOp);

   ------------------------------------------------------------------
   -- ProgressAdminActivity
   --
   -- Description:
   --    Progresses a admin activity that has already started.
   --
   -- Traceunit : C.Enclave.ProgressAdminActivity
   -- Traceto : FD.Enclave.ValidateAdminTokenOK
   -- Traceto : FD.Enclave.ValidateAdminTokenFail
   -- Traceto : FD.Enclave.FailedAdminTokenRemoval
   -- Traceto : FD.Enclave.TISAdminLogin
   -- Traceto : FD.Enclave.TISCompleteTimoutAdminLogout
   -- Traceto : FD.Enclave.TISArchiveLogOp
   -- Traceto : FD.Enclave.StartArchiveLogOK
   -- Traceto : FD.Enclave.StartArchiveLogWaitingFloppy
   -- Traceto : FD.Enclave.FinishArchiveLogOK
   -- Traceto : FD.Enclave.FinishArchiveLogNoFloppy
   -- Traceto : FD.Enclave.FinishArchiveLogBadMatch
   -- Traceto : FD.Enclave.TISUpdateConfigDataOp
   -- Traceto : FD.Enclave.StartUpdateConfigDataOK
   -- Traceto : FD.Enclave.StartUpdateConfigDataWaitingFloppy
   -- Traceto : FD.Enclave.FinishUpdateConfigDataOK
   -- Traceto : FD.Enclave.FinishUpdateConfigDataFail
   -- Traceto : FD.Enclave.TISShutdownOp
   -- Traceto : FD.Enclave.ShutdownOK
   -- Traceto : FD.Enclave.ShutdownWaitingDoor
   -- Traceto : FD.Enclave.TISUnlockDoorOp
   -- Traceto : FD.Enclave.OverrideDoorLockOK
   ------------------------------------------------------------------
   procedure ProgressAdminActivity (TheAdmin : in out Admin.T)
     with Global  => (Input  => (AdminToken.Input,
                                 Clock.CurrentTime,
                                 Clock.Now,
                                 Floppy.Input,
                                 KeyStore.State,
                                 KeyStore.Store),
                      In_Out => (AdminToken.State,
                                 AdminToken.Status,
                                 AuditLog.FileState,
                                 AuditLog.State,
                                 ConfigData.FileState,
                                 ConfigData.State,
                                 Display.State,
                                 Door.State,
                                 Floppy.Output,
                                 Floppy.State,
                                 Floppy.WrittenState,
                                 Latch.State,
                                 Screen.State,
                                 State,
                                 UserToken.State)),
          Depends => ((AdminToken.State,
                       TheAdmin)             => (AdminToken.Input,
                                                 AdminToken.State,
                                                 AdminToken.Status,
                                                 Clock.CurrentTime,
                                                 Door.State,
                                                 KeyStore.State,
                                                 KeyStore.Store,
                                                 State,
                                                 TheAdmin),
                      AdminToken.Status      =>+ (AdminToken.State,
                                                  State),
                      (AuditLog.FileState,
                       AuditLog.State)       => (AdminToken.Input,
                                                 AdminToken.State,
                                                 AdminToken.Status,
                                                 AuditLog.FileState,
                                                 AuditLog.State,
                                                 Clock.CurrentTime,
                                                 Clock.Now,
                                                 ConfigData.FileState,
                                                 ConfigData.State,
                                                 Display.State,
                                                 Door.State,
                                                 Floppy.Input,
                                                 Floppy.State,
                                                 Floppy.WrittenState,
                                                 KeyStore.State,
                                                 KeyStore.Store,
                                                 Latch.State,
                                                 Screen.State,
                                                 State,
                                                 TheAdmin),
                      (ConfigData.FileState,
                       ConfigData.State)     =>+ (Floppy.State,
                                                  State,
                                                  TheAdmin),
                      (Display.State,
                       UserToken.State)      =>+ (Door.State,
                                                  State,
                                                  TheAdmin),
                      (Door.State,
                       Latch.State)          => (Clock.CurrentTime,
                                                 ConfigData.State,
                                                 Door.State,
                                                 Latch.State,
                                                 State,
                                                 TheAdmin),
                      Floppy.Output          =>+ (AuditLog.FileState,
                                                  AuditLog.State,
                                                  Floppy.State,
                                                  State,
                                                  TheAdmin),
                      Floppy.State           =>+ (Floppy.Input,
                                                  State,
                                                  TheAdmin),
                      Floppy.WrittenState    =>+ (AuditLog.FileState,
                                                  AuditLog.State,
                                                  Floppy.State,
                                                  State,
                                                  TheAdmin),
                      Screen.State           =>+ (AdminToken.Input,
                                                  AdminToken.State,
                                                  AdminToken.Status,
                                                  Clock.CurrentTime,
                                                  Door.State,
                                                  Floppy.Input,
                                                  Floppy.State,
                                                  Floppy.WrittenState,
                                                  KeyStore.State,
                                                  KeyStore.Store,
                                                  State,
                                                  TheAdmin),
                      State                  =>+ (AdminToken.Input,
                                                  AdminToken.State,
                                                  AdminToken.Status,
                                                  Clock.CurrentTime,
                                                  Door.State,
                                                  Floppy.State,
                                                  KeyStore.State,
                                                  KeyStore.Store,
                                                  TheAdmin)),
          --------------------------------------------------------
          -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
          --====================================================--
          -- Before each call to ProgressAdminActivity, the     --
          -- security property holds.                           --
          --------------------------------------------------------
          Pre     =>
            not EnrolmentIsInProgress and
            CurrentAdminActivityPossible and

            ((Latch.IsLocked and
                Door.TheCurrentDoor = Door.Open and
                Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
                                         Door.Alarm_Timeout)) =
               (Door.TheDoorAlarm = AlarmTypes.Alarming)) and

            (if (statusIsGotAdminToken or
                   statusIsWaitingRemoveAdminTokenFail)
             then
                not Admin.IsPresent(TheAdmin)) and

            (if not Admin.IsPresent(TheAdmin) then
                not Admin.IsDoingOp(TheAdmin)) and

            (if (statusIsWaitingStartAdminOp or
                   statusIsWaitingFinishAdminOp)
             then
                (Admin.IsPresent(TheAdmin) and
                   Admin.IsDoingOp(TheAdmin))) and

            (if statusIsEnclaveQuiescent then
                not Admin.IsDoingOp(TheAdmin)) and

            (if statusIsShutdown then
                (not Admin.IsDoingOp(TheAdmin) and
                   Admin.RolePresent(TheAdmin) = PrivTypes.UserOnly)) and

            (if (Admin.IsDoingOp(TheAdmin) and then
                   Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp)
             then
                statusIsWaitingStartAdminOp) and

            (if Admin.RolePresent(TheAdmin) = PrivTypes.Guard then
                (AdminToken.IsGood and
                   AdminToken.AuthCertValid and
                   AdminToken.TheAuthCertRole = PrivTypes.Guard)) and

            (if (Admin.IsDoingOp(TheAdmin) and then
                   Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock)
             then
                 Admin.RolePresent(TheAdmin) = PrivTypes.Guard) and

            (if Admin.RolePresent(TheAdmin) = PrivTypes.Guard then
                ((Admin.IsDoingOp(TheAdmin) and then
                    Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock) or
                   not Admin.IsDoingOp(TheAdmin))),
          --------------------------------------------------------
          -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
          --====================================================--
          -- After each call to ProgressAdminActivity, the      --
          -- security property holds.                           --
          --------------------------------------------------------
          Post    =>
            not EnrolmentIsInProgress and

            ((Latch.IsLocked and
                Door.TheCurrentDoor = Door.Open and
                Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
                                         Door.Alarm_Timeout)) =
               (Door.TheDoorAlarm = AlarmTypes.Alarming)) and

            (if (statusIsGotAdminToken or
                   statusIsWaitingRemoveAdminTokenFail)
             then
                not Admin.IsPresent(TheAdmin)) and

            (if (statusIsWaitingStartAdminOp or
                   statusIsWaitingFinishAdminOp)
             then
                (Admin.IsDoingOp(TheAdmin) and
                   Admin.IsPresent(TheAdmin) and
                   Admin.RolePresent(TheAdmin) =
                   Admin.RolePresent(TheAdmin'Old))) and

            (if statusIsEnclaveQuiescent then
                not Admin.IsDoingOp(TheAdmin)) and

            (if statusIsShutdown then
                (not Admin.IsDoingOp(TheAdmin) and
                   Admin.RolePresent(TheAdmin) = PrivTypes.UserOnly)) and

            (if (Admin.IsDoingOp(TheAdmin) and then
                   Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp)
             then
                 statusIsWaitingStartAdminOp) and

            (if Admin.RolePresent(TheAdmin) = PrivTypes.Guard then
                (AdminToken.IsGood and
                   AdminToken.AuthCertValid and
                   AdminToken.TheAuthCertRole = PrivTypes.Guard)) and

            (if (Admin.IsDoingOp(TheAdmin) and then
                   Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock)
             then
                 Admin.RolePresent(TheAdmin) = PrivTypes.Guard) and

            (if Admin.RolePresent(TheAdmin) = PrivTypes.Guard then
                ((Admin.IsDoingOp(TheAdmin) and then
                    Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock) or
                   not Admin.IsDoingOp(TheAdmin))) and

            (if not Admin.IsPresent(TheAdmin) then
                not Admin.IsDoingOp(TheAdmin)) and

            (if (not Latch.IsLocked and Latch.IsLocked'Old) then
                ((AdminToken.IsGood and
                    AdminToken.AuthCertValid and
                    AdminToken.TheAuthCertRole = PrivTypes.Guard))) and

            (if (not Latch.IsLocked and Latch.IsLocked'Old) then
                (Admin.IsDoingOp(TheAdmin'Old) and
                   Admin.TheCurrentOp(TheAdmin'Old) = Admin.OverrideLock));

   ------------------------------------------------------------------
   -- StartAdminActivity
   --
   -- Description:
   --    Starts a new admin operation or logon.
   --
   -- Traceunit : C.Enclave.StartAdminActivity
   -- Traceto : FD.Enclave.GetPresentAdminToken
   -- Traceto : FD.Enclave.TISStartAdminOp
   -- Traceto : FD.Enclave.ValidateOpRequestOK
   -- Traceto : FD.Enclave.ValidateOpRequestFail
   -- Traceto : FD.Enclave.NoOpRequest
   ------------------------------------------------------------------
   procedure StartAdminActivity (TheAdmin : in out Admin.T)
     with Global  => (Input  => (AdminToken.State,
                                 Clock.Now,
                                 ConfigData.State,
                                 Keyboard.Inputs),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 Screen.State,
                                 State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AdminToken.State,
                                               AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Keyboard.Inputs,
                                               Screen.State,
                                               State,
                                               TheAdmin),
                      (Screen.State,
                       State,
                       TheAdmin)           =>+ (AdminToken.State,
                                                Keyboard.Inputs,
                                                State,
                                                TheAdmin)),

          Pre     =>
            not EnrolmentIsInProgress and

            (if Admin.RolePresent (TheAdmin) = PrivTypes.Guard then
                (AdminToken.IsGood
                   and AdminToken.AuthCertValid
                   and AdminToken.TheAuthCertRole = PrivTypes.Guard)) and

            (if (Admin.IsDoingOp (TheAdmin) and then
                   Admin.TheCurrentOp (TheAdmin) = Admin.OverrideLock)
             then
                Admin.RolePresent (TheAdmin) = PrivTypes.Guard) and

            (if not Admin.IsPresent (TheAdmin) then
                not Admin.IsDoingOp (TheAdmin)) and

            (if (statusIsGotAdminToken
                   or statusIsWaitingRemoveAdminTokenFail)
             then
                not Admin.IsPresent (TheAdmin)) and

            (if (statusIsWaitingStartAdminOp
                   or statusIsWaitingFinishAdminOp)
             then
                (Admin.IsPresent (TheAdmin)
                   and Admin.IsDoingOp (TheAdmin))) and

            (if statusIsEnclaveQuiescent then
                not Admin.IsDoingOp (TheAdmin)) and

            (if statusIsShutdown then
                (not Admin.IsDoingOp (TheAdmin)
                   and Admin.RolePresent (TheAdmin) = PrivTypes.UserOnly)) and

            (if (Admin.IsDoingOp (TheAdmin)
                   and then Admin.TheCurrentOp (TheAdmin) = Admin.ShutdownOp)
             then
                statusIsWaitingStartAdminOp) and

            (if Admin.RolePresent (TheAdmin) = PrivTypes.Guard then
                ((Admin.IsDoingOp (TheAdmin)
                    and then Admin.TheCurrentOp (TheAdmin) =
                               Admin.OverrideLock)
                 or not Admin.IsDoingOp (TheAdmin))),

          Post    =>
            not EnrolmentIsInProgress and

            (if not Admin.IsPresent (TheAdmin) then
                not Admin.IsDoingOp (TheAdmin)) and

            (if (statusIsGotAdminToken or
                   statusIsWaitingRemoveAdminTokenFail)
             then
                not Admin.IsPresent (TheAdmin)) and

            (if (statusIsWaitingStartAdminOp
                   or statusIsWaitingFinishAdminOp)
             then
                (Admin.IsDoingOp (TheAdmin)
                   and Admin.IsPresent (TheAdmin)
                   and Admin.RolePresent (TheAdmin) =
                         Admin.RolePresent (TheAdmin'Old))) and

            (if statusIsEnclaveQuiescent then
                (not Admin.IsDoingOp (TheAdmin)
                   and Admin.RolePresent (TheAdmin) =
                         Admin.RolePresent (TheAdmin'Old))) and

            (if statusIsShutdown then
                (not Admin.IsDoingOp (TheAdmin)
                   and Admin.RolePresent (TheAdmin) =
                         PrivTypes.UserOnly)) and

            (if (Admin.IsDoingOp (TheAdmin)
                   and then Admin.TheCurrentOp (TheAdmin) = Admin.ShutdownOp)
             then
                statusIsWaitingStartAdminOp) and

            (if Admin.RolePresent (TheAdmin) = PrivTypes.Guard then
                (AdminToken.IsGood
                   and AdminToken.AuthCertValid
                   and AdminToken.TheAuthCertRole = PrivTypes.Guard)) and

            (if (Admin.IsDoingOp (TheAdmin)
                   and then Admin.TheCurrentOp (TheAdmin) = Admin.OverrideLock)
             then
                Admin.RolePresent (TheAdmin) = PrivTypes.Guard) and

            (if Admin.RolePresent (TheAdmin) = PrivTypes.Guard then
                ((Admin.IsDoingOp (TheAdmin)
                    and then Admin.TheCurrentOp (TheAdmin) =
                               Admin.OverrideLock)
                 or not Admin.IsDoingOp (TheAdmin)));

   ------------------------------------------------------------------
   -- ResetScreenMessage
   --
   -- Description:
   --    Resets the screen message based on the current state of
   --    the enclave.
   --
   -- Traceunit : C.Enclave.ResetScreenMessage
   -- Traceto : FD.Enclave.ResetScreenMessage
   ------------------------------------------------------------------
   procedure ResetScreenMessage (TheAdmin : in Admin.T)
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State,
                                 State),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 Screen.State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Screen.State,
                                               State,
                                               TheAdmin),
                      Screen.State         =>+ (State,
                                                TheAdmin));

private
   Status : StatusT with Part_Of => State;

   ------------------------------------------------------------------
   --  Types
   ------------------------------------------------------------------

   subtype EnrolmentStates is StatusT
     range NotEnrolled .. WaitingEndEnrol;

   subtype ActiveEnclaveStates is StatusT
     range GotAdminToken .. Shutdown;

   subtype NonQuiescentStates is StatusT
     range WaitingRemoveAdminTokenFail .. Shutdown;

   ------------------------------------------------------------------
   --  State
   ------------------------------------------------------------------
   function GetStatus return StatusT is (Status)
     with Refined_Global => Status;

   function statusIsGotAdminToken return Boolean is
     (Status = GotAdminToken)
     with Refined_Global => Status;

   function statusIsWaitingRemoveAdminTokenFail return Boolean is
     (Status = WaitingRemoveAdminTokenFail)
     with Refined_Global => Status;

   function statusIsWaitingStartAdminOp return Boolean is
     (Status = WaitingStartAdminOp)
     with Refined_Global => Status;

   function statusIsWaitingFinishAdminOp return Boolean is
     (Status = WaitingFinishAdminOp)
     with Refined_Global => Status;

   function statusIsEnclaveQuiescent return Boolean is
     (Status = EnclaveQuiescent)
     with Refined_Global => Status;

   function statusIsShutdown return Boolean is (Status = Shutdown)
     with Refined_Global => Status;

   ------------------------------------------------------------------
   -- EnrolmentIsInProgress
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   function EnrolmentIsInProgress return Boolean is (Status in EnrolmentStates)
     with Refined_Global => Status;

end Enclave;
