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
-- Implementation Notes:
--    None.
--
------------------------------------------------------------------
with Admin,
     AuditLog,
     AuditTypes,
     CommonTypes,
     ConfigData,
     Configuration,
     Door,
     Display,
     Enrolment,
     File,
     Floppy,
     Keyboard,
     Screen,
     UserToken;

use type Admin.OpAndNullT;
use type CommonTypes.PresenceT;
use type Door.T;

package body Enclave
  with Refined_State => (State => Status)
is
   ------------------------------------------------------------------
   --  Private Operations
   --
   ------------------------------------------------------------------

   ------------------------------------------------------------------
   -- PresentAdminHasDeparted
   --
   -- Description:
   --    Returns True exactly when a logged in Administrator leaves.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   function PresentAdminHasDeparted (TheAdmin : Admin.T) return Boolean
     with Global => AdminToken.State
   is
      Result : Boolean;
   begin
      if Admin.IsPresent(TheAdmin) and not AdminToken.IsPresent then
         if not Admin.IsDoingOp(TheAdmin) or else
            Admin.TheCurrentOp(TheAdmin) /= Admin.ShutdownOp then
            Result := True;
         else
            Result := False;
         end if;
      else
         Result := False;
      end if;
      return Result;
   end PresentAdminHasDeparted;

   ------------------------------------------------------------------
   -- AdminTokenHasExpired
   --
   -- Description:
   --    Returns True exactly when a logged on administrator token
   --    expires and the administrator is not undertaking an
   --    operation.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   function AdminTokenHasExpired (TheAdmin : Admin.T) return Boolean is
     (Admin.IsPresent(TheAdmin)
        and AdminToken.IsPresent
        and Status = EnclaveQuiescent
        and not AdminToken.IsCurrent)
     with Global => (AdminToken.State,
                     Clock.CurrentTime,
                     Status);

   ------------------------------------------------------------------
   -- AdminHasDeparted
   --
   -- Description:
   --    Returns True exactly when the admin token is removed when in
   --    a non-quiescent state.
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   function AdminHasDeparted return Boolean is
     (not AdminToken.IsPresent
        and Status in NonQuiescentStates)
     with Global => (AdminToken.State,
                     Status);

   ------------------------------------------------------------------
   -- ReadEnrolmentData
   --
   -- Description:
   --    Attempts to read the enrolment file if a floppy is present
   --
   -- Implementation Notes:
   --    None.
   --
   -- Traceunit : C.Enclave.ReadEnrolmentData
   -- Traceto : FD.Enclave.RequestEnrolment
   -- Traceto : FD.Enclave.ReadEnrolmentFloppy
   ------------------------------------------------------------------
   procedure ReadEnrolmentData
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State,
                                 Floppy.Input),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 Display.State,
                                 Floppy.State,
                                 Screen.State,
                                 Status)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Display.State,
                                               Floppy.State,
                                               Screen.State),
                      (Display.State,
                       Screen.State,
                       Status)             =>+ Floppy.State,
                      Floppy.State         =>+ Floppy.Input),
          Pre     => Status in EnrolmentStates,
          Post    => Status in EnrolmentStates
   is
   begin
      if Floppy.IsPresent then

         -- ReadEnrolmentFloppyC actions
         Floppy.Read;
         Screen.SetMessage(Msg => Screen.ValidatingEnrolmentData);
         Display.SetValue(Msg => Display.Blank);

         Status := WaitingEnrol;

      else
         -- RequestEnrolmentC actions
         Screen.SetMessage(Msg => Screen.InsertEnrolmentData);
         Display.SetValue(Msg => Display.Blank);

      end if;
   end ReadEnrolmentData;

   ------------------------------------------------------------------
   -- ValidateEnrolmentData
   --
   -- Description:
   --    Attempts to validate the enrolment data
   --
   -- Implementation Notes:
   --    Note that UserEntry.Status is initialized to Quiescent.
   --
   -- Traceunit : C.Enclave.ValidateEnrolmentData
   -- Traceto : FD.Enclave.ValidateEnrolmentDataOK
   -- Traceto : FD.Enclave.ValidateEnrolmentDataFail
   ------------------------------------------------------------------
   procedure ValidateEnrolmentData
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State,
                                 Floppy.State),
                      Output => Status,
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 Display.State,
                                 KeyStore.State,
                                 KeyStore.Store,
                                 Screen.State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Display.State,
                                               Floppy.State,
                                               KeyStore.Store,
                                               Screen.State),
                      (Display.State,
                       KeyStore.State,
                       KeyStore.Store,
                       Screen.State)       =>+ (Floppy.State,
                                                KeyStore.Store),
                      Status               => (Floppy.State,
                                               KeyStore.Store)),
          Pre     => not KeyStore.PrivateKeyPresent,
          Post    => (Status = EnclaveQuiescent and
                        KeyStore.PrivateKeyPresent)
                     or (Status = WaitingEndEnrol and
                           not KeyStore.PrivateKeyPresent)
   is
      TheCurrentFloppy : File.T;
      DataOK           : Boolean;
      Description      : AuditTypes.DescriptionT;
   begin
      TheCurrentFloppy := Floppy.CurrentFloppy;

      pragma Warnings (Off);
      Enrolment.Validate(TheFile     => TheCurrentFloppy,
                         DataOK      => DataOK,
                         Description => Description);
      pragma Warnings (On);

      if DataOK then

         -- ValidateEnrolmentDataOK actions
         Screen.SetMessage(Msg => Screen.WelcomeAdmin);
         Display.SetValue(Msg => Display.Welcome);
         Status := EnclaveQuiescent;

         AuditLog.AddElementToLog
           (ElementID   => AuditTypes.EnrolmentComplete,
            Severity    => AuditTypes.Information,
            User        => AuditTypes.NoUser,
            Description => AuditTypes.NoDescription);

      else
         -- ValidateEnrolmentDataFail actions
         Screen.SetMessage(Msg => Screen.EnrolmentFailed);
         Display.SetValue(Msg => Display.Blank);
         Status := WaitingEndEnrol;

         AuditLog.AddElementToLog
           (ElementID   => AuditTypes.EnrolmentFailed,
            Severity    => AuditTypes.Warning,
            User        => AuditTypes.NoUser,
            Description => Description);

      end if;
   end ValidateEnrolmentData;

   ------------------------------------------------------------------
   -- CompleteFailedEnrolment
   --
   -- Description:
   --    Performes actions when the enclave status is WaitingEndEnrol
   --
   -- Implementation Notes:
   --    None
   --
   -- Traceunit : C.Enclave.CompleteFailedEnrolment
   -- Traceto : FD.Enclave.FailedEnrolFloppyRemoved
   -- Traceto : FD.Enclave.WaitingFloppyRemoval
   ------------------------------------------------------------------
   procedure CompleteFailedEnrolment
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State,
                                 Floppy.State),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 Display.State,
                                 Screen.State,
                                 Status)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Display.State,
                                               Floppy.State,
                                               Screen.State),
                      (Display.State,
                       Screen.State,
                       Status)             =>+ Floppy.State),
          Pre     => Status = WaitingEndEnrol,
          Post    => Status = WaitingEndEnrol or Status = NotEnrolled
   is
   begin
      if not Floppy.IsPresent then

         -- FailedEnrolFloppyRemoved actions
         Screen.SetMessage(Msg => Screen.InsertEnrolmentData);
         Display.SetValue(Msg => Display.Blank);

         Status := NotEnrolled;

      end if; -- else WaitingFloppyRemoval (no actions)

   end CompleteFailedEnrolment;

   ------------------------------------------------------------------
   -- AdminTokenTear
   --
   -- Description:
   --    Handles an admin token tear.
   --
   -- Implementation Notes:
   --    Setting of the screen message is postponed to TIS since
   --    we cannot determine whether there is a user entry in progress
   --    from here.
   --
   ------------------------------------------------------------------
   procedure AdminTokenTear
     with Global  => (In_Out => AdminToken.State),
          Depends => (AdminToken.State =>+ null)
   is
   begin
      AdminToken.Clear;
   end AdminTokenTear;

   ------------------------------------------------------------------
   -- BadAdminTokenTear
   --
   -- Description:
   --    Handles a bad admin token tear.
   --
   -- Implementation Notes:
   --    Note that we can deduce the screen message since BadAdminTokenTears
   --    only occur when the Admin is active and hence user entry is not
   --    in progress.
   --
   -- Traceunit : C.Enclave.BadAdminTokenTear
   -- Traceto : FD.Enclave.LoginAborted
   -- Traceto : FD.Enclave.BadAdminLogout
   ------------------------------------------------------------------
   procedure BadAdminTokenTear
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State),
                      Output => Status,
                      In_Out => (AdminToken.State,
                                 AuditLog.FileState,
                                 AuditLog.State)),
          Depends => (AdminToken.State     =>+ null,
                      (AuditLog.FileState,
                       AuditLog.State)     => (AdminToken.State,
                                               AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State),
                      Status               => null),
          Post    => Status = EnclaveQuiescent
   is
      pragma Postcondition (Status = EnclaveQuiescent);
   begin

      AuditLog.AddElementToLog
        (ElementID   => AuditTypes.AdminTokenRemoved,
         Severity    => AuditTypes.Warning,
         User        => AdminToken.ExtractUser,
         Description => AuditTypes.NoDescription);

      Status := enclaveQuiescent;
      AdminTokenTear;

   end BadAdminTokenTear;

   ------------------------------------------------------------------
   -- ValidateAdminToken
   --
   -- Description:
   --    Reads and validates the administrator's token.
   --    Performs all actions when Status = GotAdminToken
   --
   -- Implementation Notes:
   --    Since it is expensive to read all the certificates from the
   --    token they are only read if required. This means that the
   --    reading of the certificates from the token is postponed until
   --    this operation.
   --
   -- Traceunit : C.Enclave.ValidateAdminToken
   -- Traceto : FD.Enclave.GetPresentAdminToken


   -- Traceto : FD.Enclave.ValidateAdminTokenOK
   -- Traceto : FD.Enclave.ValidateAdminTokenFail
   -- Traceto : FD.Enclave.LoginAborted
   ------------------------------------------------------------------
   procedure ValidateAdminToken(TheAdmin : in out Admin.T)
     with Global  => (Input  => (AdminToken.Input,
                                 Clock.CurrentTime,
                                 Clock.Now,
                                 ConfigData.State,
                                 KeyStore.State,
                                 KeyStore.Store),
                      Output => Status,
                      In_Out => (AdminToken.State,
                                 AdminToken.Status,
                                 AuditLog.FileState,
                                 AuditLog.State,
                                 Screen.State)),
          Depends => ((AdminToken.State,
                       Screen.State,
                       TheAdmin)           =>+ (AdminToken.Input,
                                                AdminToken.State,
                                                AdminToken.Status,
                                                Clock.CurrentTime,
                                                KeyStore.State,
                                                KeyStore.Store),
                      AdminToken.Status    =>+ AdminToken.State,
                      (AuditLog.FileState,
                       AuditLog.State)     => (AdminToken.Input,
                                               AdminToken.State,
                                               AdminToken.Status,
                                               AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.CurrentTime,
                                               Clock.Now,
                                               ConfigData.State,
                                               KeyStore.State,
                                               KeyStore.Store,
                                               Screen.State),
                      Status               => (AdminToken.Input,
                                               AdminToken.State,
                                               AdminToken.Status,
                                               Clock.CurrentTime,
                                               KeyStore.State,
                                               KeyStore.Store)),
          Pre     =>
     not Admin.IsPresent(TheAdmin) and
     not Admin.IsDoingOp(TheAdmin) and

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
          Post    =>
     (Status = EnclaveQuiescent or
        Status = WaitingRemoveAdminTokenFail) and

     (if Status = WaitingRemoveAdminTokenFail then
         not Admin.IsPresent(TheAdmin)) and

     not Admin.IsDoingOp(TheAdmin) and

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
            not Admin.IsDoingOp(TheAdmin)))
   is
     TokenOK     : Boolean;
     Description : AuditTypes.DescriptionT;
   begin

      if not AdminToken.IsPresent then

         -- LoginAbortedC actions
         BadAdminTokenTear;

      else

         AdminToken.ReadAndCheck (Description => Description,
                                  TokenOK     => TokenOk);

         -- GetPresentAdminTokenC postponed actions
         AuditLog.AddElementToLog
           (ElementID   => AuditTypes.AdminTokenPresent,
            Severity    => AuditTypes.Information,
            User        => AdminToken.ExtractUser,
            Description => AuditTypes.NoDescription);

         if TokenOK then

            -- ValidateAdminTokenOKC actions
            AuditLog.AddElementToLog
              (ElementID   => AuditTypes.AdminTokenValid,
               Severity    => AuditTypes.Information,
               User        => AdminToken.ExtractUser,
               Description => AuditTypes.NoDescription);

            Screen.SetMessage (Msg => Screen.RequestAdminOp);
            Status := EnclaveQuiescent;

            Admin.Logon (TheAdmin => TheAdmin,
                         Role     => AdminToken.GetRole);

         else

            -- ValidateAdminTokenFailC actions

            AuditLog.AddElementToLog
              (ElementID   => AuditTypes.AdminTokenInvalid,
               Severity    => AuditTypes.Warning,
               User        => AdminToken.ExtractUser,
               Description => Description);

            Screen.SetMessage (Msg => Screen.RemoveAdminToken);
            Status := WaitingRemoveAdminTokenFail;

         end if;
      end if;
   end ValidateAdminToken;

   ------------------------------------------------------------------
   -- CompleteFailedAdminLogon
   --
   -- Description:
   --    Handles the removal of the administrator's token after a
   --    failed logon.
   --
   -- Implementation Notes:
   --    None
   --
   -- Traceunit : C.Enclave.CompleteFailedAdminLogon
   -- Traceto: FD.Enclave.FailedAdminTokenRemoved
   ------------------------------------------------------------------
   procedure CompleteFailedAdminLogon
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State),
                      Output => Status,
                      In_Out => (AdminToken.State,
                                 AuditLog.FileState,
                                 AuditLog.State,
                                 Screen.State)),
          Depends => ((AdminToken.State,
                       Screen.State)       =>+ null,
                      (AuditLog.FileState,
                       AuditLog.State)     => (AdminToken.State,
                                               AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Screen.State),
                      Status               => null),
           Post    => Status = EnclaveQuiescent
   is
   begin

      AuditLog.AddElementToLog
        (ElementID   => AuditTypes.AdminTokenRemoved,
         Severity    => AuditTypes.Information,
         User        => AdminToken.ExtractUser,
         Description => AuditTypes.NoDescription);

      Status := EnclaveQuiescent;
      Screen.SetMessage(Msg => Screen.WelcomeAdmin);

      AdminToken.Clear;

   end CompleteFailedAdminLogon;

   ------------------------------------------------------------------
   -- ArchiveLogOp
   --
   -- Description:
   --    Performs the "archive log" operation
   --
   -- Implementation Notes:
   --    None
   --
   -- Traceunit : C.Enclave.ArchiveLogOp
   -- Traceto: FD.Enclave.TISArchiveLogOp
   -- Traceto: FD.Enclave.StartArchiveLogOK
   -- Traceto: FD.Enclave.StartArchiveLogWaitingFloppy
   -- Traceto: FD.Enclave.FinishArchiveLogOK
   -- Traceto: FD.Enclave.FinishArchiveLogNoFloppy
   -- Traceto: FD.Enclave.FinishArchiveLogBadMatch
   ------------------------------------------------------------------
   procedure ArchiveLogOp(TheAdmin : in out Admin.T)
     with Global  => (Input  => (AdminToken.State,
                                 Clock.Now,
                                 ConfigData.State,
                                 Floppy.Input),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 Floppy.Output,
                                 Floppy.State,
                                 Floppy.WrittenState,
                                 Screen.State,
                                 Status)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AdminToken.State,
                                               AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Floppy.Input,
                                               Floppy.State,
                                               Floppy.WrittenState,
                                               Screen.State, Status),
                      Floppy.Output        =>+ (AuditLog.FileState,
                                                AuditLog.State,
                                                Floppy.State,
                                                Status),
                      (Floppy.State,
                       TheAdmin)           =>+ Status,
                      Floppy.WrittenState  =>+ (AuditLog.FileState,
                                                AuditLog.State,
                                                Floppy.State,
                                                Status),
                      Screen.State         =>+ (Floppy.Input,
                                                Floppy.State,
                                                Floppy.WrittenState,
                                                Status),
                      Status               =>+ Floppy.State),
          Pre     =>
     (Status = WaitingStartAdminOp or
        Status = WaitingFinishAdminOp) and then

     Admin.IsPresent(TheAdmin) and then
     Admin.IsDoingOp(TheAdmin) and then
     Admin.TheCurrentOp(TheAdmin) = Admin.ArchiveLog and then

     (if Admin.RolePresent(TheAdmin) = PrivTypes.Guard then
         (AdminToken.IsGood and
            AdminToken.AuthCertValid and
            AdminToken.TheAuthCertRole = PrivTypes.Guard)) and then

     (if (Admin.IsDoingOp(TheAdmin) and then
            Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock)
      then
         Admin.RolePresent(TheAdmin) = PrivTypes.Guard) and then

     (if Admin.RolePresent(TheAdmin) = PrivTypes.Guard then
         ((Admin.IsDoingOp(TheAdmin) and then
             Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock) or
            not Admin.IsDoingOp(TheAdmin))),
          Post    =>
     (Status = WaitingStartAdminOp or
        Status = WaitingFinishAdminOp or
        Status = EnclaveQuiescent) and

     Admin.IsPresent(TheAdmin) and

     (if (Status = WaitingStartAdminOp or
            Status = WaitingFinishAdminOp )
      then
         (Admin.IsDoingOp(TheAdmin) and
            Admin.IsPresent(TheAdmin) and
            Admin.TheCurrentOp(TheAdmin) = Admin.ArchiveLog)) and

     (if Status = EnclaveQuiescent then
         not Admin.IsDoingOp(TheAdmin)) and

     (if Admin.RolePresent(TheAdmin) = PrivTypes.Guard then
         (AdminToken.IsGood and
            AdminToken.AuthCertValid and
            AdminToken.TheAuthCertRole = PrivTypes.Guard)) and

     (if (Admin.IsDoingOp(TheAdmin) and then
            Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock)
      then
         Admin.RolePresent(TheAdmin) = PrivTypes.Guard) and

     (if Admin.RolePresent(TheAdmin) = PrivTypes.Guard then
         ((Admin.IsDoingOp(TheAdmin) and
             Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock) or
            not Admin.IsDoingOp(TheAdmin))) and

     Admin.RolePresent(TheAdmin) = Admin.RolePresent(TheAdmin'Old)
   is
      ------------------------------------------------------------------
      -- StartArchiveLog
      --
      -- Description:
      --    Starts the "archive log" operation
      --
      -- Implementation Notes:
      --    None
      --
      -- Traceunit : C.Enclave.ArchiveLogOp.StartArchiveLog
      -- Traceto: FD.Enclave.StartArchiveLogOK
      -- Traceto: FD.Enclave.StartArchiveLogWaitingFloppy
      ------------------------------------------------------------------
      procedure StartArchiveLog
        with Global  => (Input  => (AdminToken.State,
                                    Clock.Now,
                                    ConfigData.State),
                         In_Out => (AuditLog.FileState,
                                    AuditLog.State,
                                    Floppy.Output,
                                    Floppy.State,
                                    Floppy.WrittenState,
                                    Screen.State,
                                    Status)),
             Depends => ((AuditLog.FileState,
                          AuditLog.State)     => (AdminToken.State,
                                                  AuditLog.FileState,
                                                  AuditLog.State,
                                                  Clock.Now,
                                                  ConfigData.State,
                                                  Floppy.State,
                                                  Screen.State),
                         Floppy.Output        =>+ (AuditLog.FileState,
                                                   AuditLog.State,
                                                   Floppy.State),
                         (Floppy.State,
                          Screen.State,
                          Status)             =>+ Floppy.State,
                         Floppy.WrittenState  =>+ (AuditLog.FileState,
                                                   AuditLog.State,
                                                   Floppy.State)),
             Pre     => Status = WaitingStartAdminOp,
             Post    => Status = WaitingStartAdminOp
                          or Status = WaitingFinishAdminOp
      is
         TheLog : File.T;
      begin
         if Floppy.IsPresent then

            -- StartArchiveLogOK actions
            AuditLog.ArchiveLog(User    => AdminToken.ExtractUser,
                                Archive => TheLog);
            Screen.SetMessage(Msg => Screen.DoingOp);
            Status := WaitingFinishAdminOp;

            -- UpdateFloppy
            Floppy.Write(TheFile => TheLog);
         else
            -- StartArchiveLogWaitingFloppy actions
            Screen.SetMessage(Msg => Screen.InsertBlankFloppy);
         end if;
      end StartArchiveLog;

      ------------------------------------------------------------------
      -- FinishArchiveLog
      --
      -- Description:
      --    Finishes the "archive log" operation
      --
      -- Implementation Notes:
      --    None
      --
      -- Traceunit : C.Enclave.ArchiveLogOp.FinishArchiveLog
      -- Traceto: FD.Enclave.FinishArchiveLogOK
      -- Traceto: FD.Enclave.FinishArchiveLogNoFloppy
      -- Traceto: FD.Enclave.FinishArchiveLogBadMatch
      ------------------------------------------------------------------
      procedure FinishArchiveLog
        with Global  => (Input  => (AdminToken.State,
                                    Clock.Now,
                                    ConfigData.State,
                                    Floppy.Input),
                         Output => Status,
                         In_Out => (AuditLog.FileState,
                                    AuditLog.State,
                                    Floppy.State,
                                    Floppy.WrittenState,
                                    Screen.State,
                                    TheAdmin)),
             Depends => ((AuditLog.FileState,
                          AuditLog.State)     => (AdminToken.State,
                                                  AuditLog.FileState,
                                                  AuditLog.State,
                                                  Clock.Now,
                                                  ConfigData.State,
                                                  Floppy.Input,
                                                  Floppy.State,
                                                  Floppy.WrittenState,
                                                  Screen.State),
                         (Floppy.State,
                          TheAdmin)           =>+ null,
                         Floppy.WrittenState  =>+ Floppy.State,
                         Screen.State         =>+ (Floppy.Input,
                                                   Floppy.State,
                                                   Floppy.WrittenState),
                         Status => null),
              Pre     => Admin.IsPresent(TheAdmin),
              Post    => Status = EnclaveQuiescent and
                         Admin.IsPresent(TheAdmin) and
                         not Admin.IsDoingOp(TheAdmin) and
                         Admin.RolePresent(TheAdmin) =
                           Admin.RolePresent(TheAdmin'Old)
      is
         WriteOK : Boolean;
      begin
         if Floppy.IsPresent then

            Floppy.Read;
            Floppy.CheckWrite(WriteOK => WriteOK);

            if WriteOK then
               -- FinishArchiveLogOK unique actions
               AuditLog.ClearLogEntries (User => AdminToken.ExtractUser);
               Screen.SetMessage(Msg => Screen.RequestAdminOp);
            else
               -- FinishArchiveLogBadMatch unique actions
               AuditLog.CancelArchive;

               AuditLog.AddElementToLog
                 (ElementID   => AuditTypes.ArchiveCheckFailed,
                  Severity    => AuditTypes.Warning,
                  User        => AdminToken.ExtractUser,
                  Description => "Archive Cancelled - Floppy has bad data");

               Screen.SetMessage(Msg => Screen.ArchiveFailed);

            end if;

         else
            -- FinishArchiveLogNoFloppy unique actions
            AuditLog.CancelArchive;

            AuditLog.AddElementToLog
              (ElementID   => AuditTypes.ArchiveCheckFailed,
               Severity    => AuditTypes.Warning,
               User        => AdminToken.ExtractUser,
               Description => "Archive Cancelled - Floppy has been removed");

            Screen.SetMessage(Msg => Screen.ArchiveFailed);
         end if;

         -- FinishArchiveLog common actions

         Status := EnclaveQuiescent;

         Admin.FinishOp(TheAdmin => TheAdmin);
      end FinishArchiveLog;

   ------------------------
   -- begin ArchiveLogOp --
   ------------------------
   begin
      if Status = WaitingStartAdminOp then
         StartArchiveLog;
      else
         FinishArchiveLog;
      end if;
   end ArchiveLogOp;

   ------------------------------------------------------------------
   -- UpdateConfigDataOp
   --
   -- Description:
   --    Performs the "update config data" operation
   --    May raise SystemFault.
   --
   -- Implementation Notes:
   --    The Configuration utility layer performs the audit actions
   --
   -- Traceunit : C.Enclave.UpdateConfigDataOp
   -- Traceto: FD.Enclave.TISUpdateConfigDataOp
   -- Traceto: FD.Enclave.StartUpdateConfigDataOK
   -- Traceto: FD.Enclave.StartUpdateConfigWaitingFloppy
   -- Traceto: FD.Enclave.FinishUpdateConfigDataOK
   -- Traceto: FD.Enclave.FinishUpdateConfigDataFail
   ------------------------------------------------------------------
   procedure UpdateConfigDataOp (TheAdmin : in out Admin.T)
     with Global  => (Input  => (AdminToken.State,
                                 Clock.Now,
                                 Floppy.Input),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 ConfigData.FileState,
                                 ConfigData.State,
                                 Floppy.State,
                                 Screen.State,
                                 Status)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)       => (AdminToken.State,
                                                 AuditLog.FileState,
                                                 AuditLog.State,
                                                 Clock.Now,
                                                 ConfigData.FileState,
                                                 ConfigData.State,
                                                 Floppy.State,
                                                 Screen.State,
                                                 Status),
                      (ConfigData.FileState,
                       ConfigData.State,
                       Screen.State,
                       Status)               =>+ (Floppy.State,
                                                  Status),
                      Floppy.State           =>+ (Floppy.Input,
                                                  Status),
                      TheAdmin               =>+ Status),
          Pre     => (Status = WaitingStartAdminOp or
                        Status = WaitingFinishAdminOp) and then
                     Admin.IsPresent(TheAdmin) and then
                     Admin.IsDoingOp(TheAdmin) and then
                     Admin.TheCurrentOp(TheAdmin) = Admin.UpdateConfigData,
          Post    =>
     (Status = WaitingStartAdminOp or
        Status = WaitingFinishAdminOp or
        Status = EnclaveQuiescent) and

     Admin.IsPresent(TheAdmin) and

     (if (Status = WaitingStartAdminOp or
            Status = WaitingFinishAdminOp)
      then
         (Admin.IsDoingOp(TheAdmin) and
            Admin.IsPresent(TheAdmin) and
            Admin.TheCurrentOp(TheAdmin) = Admin.UpdateConfigData)) and

     (if Status = EnclaveQuiescent then
         not Admin.IsDoingOp(TheAdmin)) and

     Admin.RolePresent(TheAdmin) = Admin.RolePresent(TheAdmin'Old)
   is
      TheCurrentFloppy : File.T;
      ConfigDataOK     : Boolean;
   begin
      if Status = WaitingStartAdminOp then

         -- StartUpdateConfigDataC
         if Floppy.IsPresent then

            -- StartUpdateConfigDataOK actions
            Floppy.Read;
            Screen.SetMessage(Msg => Screen.DoingOp);
            Status := WaitingFinishAdminOp;
         else
            -- StartUpdateConfigWaitingFloppy actions
            Screen.SetMessage(Msg => Screen.InsertConfigData);
         end if;

      else
         -- FinishUpdateConfigDataC
         TheCurrentFloppy := Floppy.CurrentFloppy;

         pragma Warnings (Off);
         Configuration.UpdateData
           (TheFile   => TheCurrentFloppy,
            DataValid => ConfigDataOK);
         pragma Warnings (On);

         if ConfigDataOK then
            Screen.SetMessage(Msg => Screen.RequestAdminOp);
         else
            Screen.SetMessage(Msg => Screen.InvalidData);
         end if;
         Status := EnclaveQuiescent;

         Admin.FinishOp(TheAdmin => TheAdmin);
      end if;

   end UpdateConfigDataOp;

   ------------------------------------------------------------------
   -- OverrideDoorLockOp
   --
   -- Description:
   --    Performs the "override door lock" operation
   --
   -- Implementation Notes:
   --    None
   --
   -- Traceunit : C.Enclave.OverrideDoorLockOp
   -- Traceto: FD.Enclave.TISUnlockDoorOp
   -- Traceto: FD.Enclave.OverrideDoorLockOK
   ------------------------------------------------------------------
   procedure OverrideDoorLockOp (TheAdmin : in out Admin.T)
     with Global  => (Input  => (AdminToken.State,
                                 Clock.CurrentTime,
                                 Clock.Now,
                                 ConfigData.State),
                      Output => Status,
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 Display.State,
                                 Door.State,
                                 Latch.State,
                                 Screen.State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AdminToken.State,
                                               AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.CurrentTime,
                                               Clock.Now,
                                               ConfigData.State,
                                               Display.State,
                                               Door.State,
                                               Latch.State,
                                               Screen.State),
                      (Display.State,
                       Screen.State,
                       TheAdmin)           =>+ null,
                      (Door.State,
                       Latch.State)        =>+ (Clock.CurrentTime,
                                                ConfigData.State,
                                                Latch.State),
                      Status               => null),
           Pre     =>
     Admin.IsDoingOp(TheAdmin) and then
     Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock and then
     Admin.RolePresent(TheAdmin) = PrivTypes.Guard and then

     (if Admin.RolePresent(TheAdmin) = PrivTypes.Guard then
         (AdminToken.IsGood and
            AdminToken.AuthCertValid and
            AdminToken.TheAuthCertRole = PrivTypes.Guard)) and then

     (if (Admin.IsDoingOp(TheAdmin) and then
            Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock)
      then
         Admin.RolePresent(TheAdmin) = PrivTypes.Guard) and then

     (if Admin.RolePresent(TheAdmin) = PrivTypes.Guard then
         ((Admin.IsDoingOp(TheAdmin) and then
             Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock) or
            not Admin.IsDoingOp(TheAdmin))),
           --------------------------------------------------------
           -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
           --====================================================--
           -- After each call to OverrideDoorLockOp, the         --
           -- security property holds.                           --
           --------------------------------------------------------
           Post    =>
     Status = EnclaveQuiescent and

     ((Latch.IsLocked and
         Door.TheCurrentDoor = Door.Open and
         Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
                                  Door.Alarm_Timeout)) =
        (Door.TheDoorAlarm = AlarmTypes.Alarming)) and

     Admin.RolePresent(TheAdmin) = Admin.RolePresent(TheAdmin'Old) and
     not Admin.IsDoingOp(TheAdmin) and

     (if Admin.RolePresent(TheAdmin) = PrivTypes.Guard then
       (AdminToken.IsGood and
          AdminToken.AuthCertValid and
          AdminToken.TheAuthCertRole = PrivTypes.Guard)) and

     (if (not Latch.IsLocked and Latch.IsLocked'Old) then
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

     (if (not Latch.IsLocked and Latch.IsLocked'Old) then
         (Admin.IsDoingOp(TheAdmin'Old) and
            Admin.TheCurrentOp(TheAdmin'Old) = Admin.OverrideLock))
   is
   begin
      AuditLog.AddElementToLog
        (ElementID   => AuditTypes.OverrideLock,
         Severity    => AuditTypes.Information,
         User        => AdminToken.ExtractUser,
         Description => AuditTypes.NoDescription);

      Screen.SetMessage(Msg => Screen.RequestAdminOp);
      Display.SetValue(Msg => Display.DoorUnlocked);
      Status := EnclaveQuiescent;

      Door.UnlockDoor;
      Admin.FinishOp(TheAdmin => TheAdmin);

   end OverrideDoorLockOp;

   ------------------------------------------------------------------
   -- ShutdownOp
   --
   -- Description:
   --    Performs the shutdown operation
   --
   -- Implementation Notes:
   --    None
   --
   -- Traceunit : C.Enclave.ShutdownOp
   -- Traceto : FD.Enclave.TISShutdownOp
   -- Traceto : FD.Enclave.ShutdownOK
   -- Traceto : FD.Enclave.ShutdownWaitingDoor
   ------------------------------------------------------------------
   procedure ShutdownOp(TheAdmin : in out Admin.T)
     with Global  => (Input  => (Clock.CurrentTime,
                                 Clock.Now,
                                 ConfigData.State),
                      In_Out => (AdminToken.State,
                                 AuditLog.FileState,
                                 AuditLog.State,
                                 Display.State,
                                 Door.State,
                                 Latch.State,
                                 Screen.State,
                                 Status,
                                 UserToken.State)),
          Depends => ((AdminToken.State,
                       Display.State,
                       Screen.State,
                       Status,
                       TheAdmin,
                       UserToken.State)    =>+ Door.State,
                      (AuditLog.FileState,
                       AuditLog.State)     => (AdminToken.State,
                                               AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.CurrentTime,
                                               Clock.Now,
                                               ConfigData.State,
                                               Display.State,
                                               Door.State,
                                               Latch.State,
                                               Screen.State),
                      (Door.State,
                       Latch.State)        => (Clock.CurrentTime,
                                               Door.State,
                                               Latch.State)),
          --------------------------------------------------------
          -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
          --====================================================--
          -- Before each call to ShutdownOp, the security       --
          -- property holds.                                    --
          --------------------------------------------------------
          Pre     =>
     Status = WaitingStartAdminOp and then

     Admin.IsPresent(TheAdmin) and then
     Admin.IsDoingOp(TheAdmin) and then
     Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp and then

     ((Latch.IsLocked and
         Door.TheCurrentDoor = Door.Open and
         Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
                                  Door.Alarm_Timeout)) =
        (Door.TheDoorAlarm = AlarmTypes.Alarming)) and then

     (if Admin.RolePresent(TheAdmin) = PrivTypes.Guard then
         (AdminToken.IsGood and
            AdminToken.AuthCertValid and
            AdminToken.TheAuthCertRole = PrivTypes.Guard)) and then

     (if Admin.RolePresent(TheAdmin) = PrivTypes.Guard then
         ((Admin.IsDoingOp(TheAdmin) and then
             Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock) or
            not Admin.IsDoingOp(TheAdmin))),
          --------------------------------------------------------
          -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
          --====================================================--
          -- After each call to ShutdownOp, the security        --
          -- property holds.                                    --
          --------------------------------------------------------
          Post    =>
     (Status = Shutdown or
        Status = WaitingStartAdminOp) and

     (not (Status = WaitingStartAdminOp) or
         (Admin.RolePresent(TheAdmin) = Admin.RolePresent(TheAdmin'Old) and then
            Admin.IsPresent(TheAdmin) and then
            Admin.IsDoingOp(TheAdmin) and then
            Latch.Current_Latch = Latch.Current_Latch'Old and then
            Latch.Latch_Timeout = Latch.Latch_Timeout'Old and then
            Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp)) and

     (if Status = Shutdown then
         (Admin.RolePresent(TheAdmin) = PrivTypes.UserOnly and
            Latch.IsLocked and
            not Admin.IsDoingOp(TheAdmin))) and

     ((Admin.IsDoingOp(TheAdmin) and then
         Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp) =
        (Status = WaitingStartAdminOp)) and

     ((Latch.IsLocked and
         Door.TheCurrentDoor = Door.Open and
         Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
                                  Door.Alarm_Timeout)) =
        (Door.TheDoorAlarm = AlarmTypes.Alarming)) and

     (if Admin.RolePresent(TheAdmin) = PrivTypes.Guard then
         (AdminToken.IsGood and
            AdminToken.AuthCertValid and
            AdminToken.TheAuthCertRole = PrivTypes.Guard)) and

     (if (not Latch.IsLocked and Latch.IsLocked'Old) then
         ((AdminToken.IsGood and
             AdminToken.AuthCertValid and
             AdminToken.TheAuthCertRole = PrivTypes.Guard))) and

     (if (Admin.IsDoingOp(TheAdmin) and then
            Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock)
      then
          Admin.RolePresent(TheAdmin) = PrivTypes.Guard) and

     (if Admin.RolePresent(TheAdmin) = PrivTypes.Guard then
         ((Admin.IsDoingOp(TheAdmin) and
             Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock) or
            not Admin.IsDoingOp(TheAdmin)))
   is
   begin
      if Door.TheCurrentDoor = Door.Closed then

         -- ShutdownOK actions
         Screen.SetMessage(Msg => Screen.Clear);
         Display.SetValue(Msg => Display.Blank);
         Status := Shutdown;

         Door.LockDoor;
         Admin.Logout(TheAdmin => TheAdmin);

         AuditLog.AddElementToLog
           (ElementID   => AuditTypes.Shutdown,
            Severity    => AuditTypes.Information,
            User        => AdminToken.ExtractUser,
            Description => AuditTypes.NoDescription);

         UserToken.Clear;
         AdminToken.Clear;

      else
         -- ShutdownWaitingDoor actions
         Screen.SetMessage(Msg => Screen.CloseDoor);
      end if;

   end ShutdownOp;

   ------------------------------------------------------------------
   -- AdminOp
   --
   -- Description:
   --    Performs the admin operation
   --
   -- Implementation Notes:
   --    None
   --
   -- Traceunit : C.Enclave.AdminOp
   -- Traceto: FD.Enclave.TISAdminOpC
   ------------------------------------------------------------------
   procedure AdminOp(TheAdmin : in out Admin.T)
     with Global  => (Input  => (Clock.CurrentTime,
                                 Clock.Now,
                                 Floppy.Input),
                      In_Out => (AdminToken.State,
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
                                 Status,
                                 UserToken.State)),
          Depends => ((AdminToken.State,
                       Display.State,
                       UserToken.State)      =>+ (Door.State,
                                                  TheAdmin),
                      (AuditLog.FileState,
                       AuditLog.State)       => (AdminToken.State,
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
                                                 Latch.State,
                                                 Screen.State,
                                                 Status,
                                                 TheAdmin),
                      (ConfigData.FileState,
                       ConfigData.State)     =>+ (Floppy.State,
                                                  Status,
                                                  TheAdmin),
                      (Door.State,
                       Latch.State)          => (Clock.CurrentTime,
                                                 ConfigData.State,
                                                 Door.State,
                                                 Latch.State,
                                                 TheAdmin),
                      Floppy.Output          =>+ (AuditLog.FileState,
                                                  AuditLog.State,
                                                  Floppy.State,
                                                  Status,
                                                  TheAdmin),
                      Floppy.State           =>+ (Floppy.Input,
                                                  Status,
                                                  TheAdmin),
                      Floppy.WrittenState    =>+ (AuditLog.FileState,
                                                  AuditLog.State,
                                                  Floppy.State,
                                                  Status,
                                                  TheAdmin),
                      Screen.State           =>+ (Door.State,
                                                  Floppy.Input,
                                                  Floppy.State,
                                                  Floppy.WrittenState,
                                                  Status,
                                                  TheAdmin),
                      Status                 =>+ (Door.State,
                                                  Floppy.State,
                                                  TheAdmin),
                      TheAdmin               =>+ (Door.State,
                                                  Status)),
          --------------------------------------------------------
          -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
          --====================================================--
          -- Before each call to AdminOp, the security property --
          -- holds.                                             --
          --------------------------------------------------------
          Pre     =>
     (Status = WaitingStartAdminOp or
        Status = WaitingFinishAdminOp) and

     (if (Admin.IsDoingOp(TheAdmin) and then
            Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp)
      then
         Status = WaitingStartAdminOp) and

     Admin.IsPresent(TheAdmin) and
     Admin.IsDoingOp(TheAdmin) and

     ((Latch.IsLocked and
         Door.TheCurrentDoor = Door.Open and
         Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
                                  Door.Alarm_Timeout)) =
        (Door.TheDoorAlarm = AlarmTypes.Alarming)) and

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
          -- After each call to AdminOp, the security property  --
          -- holds.                                             --
          --------------------------------------------------------
          Post    =>
     (Status = WaitingStartAdminOp or
        Status = WaitingFinishAdminOp or
        Status = EnclaveQuiescent or
        Status = Shutdown) and

     (if (Status = WaitingStartAdminOp or
            Status = WaitingFinishAdminOp)
      then
          (Admin.IsDoingOp(TheAdmin) and
             Admin.IsPresent(TheAdmin) and
             Admin.RolePresent(TheAdmin) = Admin.RolePresent(TheAdmin'Old)))
      and

     (if Status = EnclaveQuiescent then
         (not Admin.IsDoingOp(TheAdmin) and
            Admin.IsPresent(TheAdmin) and
            Admin.RolePresent(TheAdmin) = Admin.RolePresent(TheAdmin'Old)))
      and

     (if Status = Shutdown then
         (not Admin.IsDoingOp(TheAdmin) and
            Admin.RolePresent(TheAdmin) = PrivTypes.UserOnly)) and

     (if (Admin.IsDoingOp(TheAdmin) and then
            Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp)
      then
          Status = WaitingStartAdminOp) and

     ((Latch.IsLocked and
         Door.TheCurrentDoor = Door.Open and
         Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
                                  Door.Alarm_Timeout)) =
        (Door.TheDoorAlarm = AlarmTypes.Alarming)) and

     (if Admin.RolePresent(TheAdmin) = PrivTypes.Guard then
         (AdminToken.IsGood and
            AdminToken.AuthCertValid and
            AdminToken.TheAuthCertRole = PrivTypes.Guard)) and

     (if (not Latch.IsLocked and Latch.IsLocked'Old) then
         ((AdminToken.IsGood and
             AdminToken.AuthCertValid and
             AdminToken.TheAuthCertRole = PrivTypes.Guard))) and

     (if (Admin.IsDoingOp(TheAdmin) and then
            Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock)
      then
          Admin.RolePresent(TheAdmin) = PrivTypes.Guard) and

     (if Admin.RolePresent(TheAdmin) = PrivTypes.Guard then
         ((Admin.IsDoingOp(TheAdmin) and then
             Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock) or
            not Admin.IsDoingOp(TheAdmin))) and

     (if (not Latch.IsLocked and Latch.IsLocked'Old) then
         (Admin.IsDoingOp(TheAdmin'Old) and then
            Admin.TheCurrentOp(TheAdmin'Old) = Admin.OverrideLock))
   is
   begin
      case Admin.TheCurrentOp(TheAdmin) is
         when Admin.ArchiveLog =>
            ArchiveLogOp(TheAdmin => TheAdmin);

         when Admin.UpdateConfigData =>
            UpdateConfigDataOp(TheAdmin => TheAdmin);

         when Admin.OverrideLock =>
            OverrideDoorLockOp(TheAdmin => TheAdmin);

         when Admin.ShutdownOp =>
            ShutdownOp(TheAdmin => TheAdmin);
      end case;
   end AdminOp;

   ------------------------------------------------------------------
   -- Exported subprocedures
   --
   ------------------------------------------------------------------
   ------------------------------------------------------------------
   -- Init
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure Init
     with Refined_Global  => (Input  => KeyStore.State,
                              Output => Status),
          Refined_Depends => (Status => KeyStore.State),
          Refined_Post    => (KeyStore.PrivateKeyPresent =
                                not EnrolmentIsInProgress) and
                             (EnrolmentIsInProgress or
                                Status = EnclaveQuiescent)
   is
   begin
      if KeyStore.PrivateKeyPresent then
         Status := EnclaveQuiescent;
      else
         Status := NotEnrolled;
      end if;
   end Init;

   ------------------------------------------------------------------
   -- AdminMustLogout
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   function AdminMustLogout (TheAdmin : Admin.T) return Boolean is
     (PresentAdminHasDeparted(TheAdmin => TheAdmin) or
        AdminTokenHasExpired(TheAdmin => TheAdmin))
     with Refined_Global  => (AdminToken.State,
                              Clock.CurrentTime,
                              Status);

   ------------------------------------------------------------------
   -- CurrentAdminActivityPossible
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   function CurrentAdminActivityPossible return Boolean
     with Refined_Global  => (AdminToken.State,
                              Status),
          Refined_Post => (if CurrentAdminActivityPossible'Result then
                             Status in NonQuiescentStates)

   is
      ------------------------------------------------------------------
      -- AdminActivityInProgress
      --
      -- Description:
      --    Returns True exactly when the current status represents
      --    present activity in the enclave.
      --
      -- Implementation Notes:
      --    None.
      ------------------------------------------------------------------
      function AdminActivityInProgress return Boolean is
        (Status in ActiveEnclaveStates)
        with Global => Status;

   ------------------------------------------------------------------
   -- begin CurrentAdminActivityPossible
   ------------------------------------------------------------------
   begin
      return AdminHasDeparted or AdminActivityInProgress;
   end CurrentAdminActivityPossible;

   ------------------------------------------------------------------
   -- HasShutdown
   --
   -- Description:
   --    Returns true if and only if the system is in a shutdown state.
   --
   -- traceunit : C.Enclave.HasShutdown
   -- traceto :
   ------------------------------------------------------------------
   function HasShutdown return Boolean is (Status = Shutdown)
     with Refined_Global => Status;

   ------------------------------------------------------------------
   -- EnrolOp
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure EnrolOp
     with Refined_Global  => (Input  => (Clock.Now,
                                         ConfigData.State,
                                         Floppy.Input),
                              In_Out => (AuditLog.FileState,
                                         AuditLog.State,
                                         Display.State,
                                         Floppy.State,
                                         KeyStore.State,
                                         KeyStore.Store,
                                         Screen.State,
                                         Status)),
          Refined_Depends => ((AuditLog.FileState,
                               AuditLog.State)     => (AuditLog.FileState,
                                                       AuditLog.State,
                                                       Clock.Now,
                                                       ConfigData.State,
                                                       Display.State,
                                                       Floppy.State,
                                                       KeyStore.Store,
                                                       Screen.State,
                                                       Status),
                              (Display.State,
                               KeyStore.State,
                               KeyStore.Store,
                               Screen.State,
                               Status)             =>+ (Floppy.State,
                                                        KeyStore.Store,
                                                        Status),
                              Floppy.State         =>+ (Floppy.Input,
                                                        Status)),
          --  Refined_Pre     => EnrolmentIsInProgress and not
          --                       KeyStore.PrivateKeyPresent,
          Refined_Post    =>  (KeyStore.PrivateKeyPresent =
                                 not EnrolmentIsInProgress) and
                              (EnrolmentIsInProgress or
                                 Status = EnclaveQuiescent)
   is
      LocalStatus : EnrolmentStates;
   begin
      LocalStatus := EnrolmentStates'(Status);

      case LocalStatus is
         when NotEnrolled =>
            ReadEnrolmentData;

         when WaitingEnrol =>
            ValidateEnrolmentData;

         when WaitingEndEnrol =>
            CompleteFailedEnrolment;

      end case;

   end EnrolOp;

   ------------------------------------------------------------------
   -- AdminLogout
   --
   -- Implementation Notes:
   --    Setting of screen message is postponed to the
   --    TIS program since we cannot determine whether the
   --    user entry is in progress from here.
   ------------------------------------------------------------------
   procedure AdminLogout (TheAdmin : in out Admin.T)
     with Refined_Global  => (Input  => (Clock.Now,
                                         ConfigData.State),
                              In_Out => (AdminToken.State,
                                         AuditLog.FileState,
                                         AuditLog.State,
                                         Status)),
          Refined_Depends => ((AdminToken.State,
                               Status)             => (AdminToken.State,
                                                       Status,
                                                       TheAdmin),
                              (AuditLog.FileState,
                               AuditLog.State)     => (AdminToken.State,
                                                       AuditLog.FileState,
                                                       AuditLog.State,
                                                       Clock.Now,
                                                       ConfigData.State,
                                                       Status,
                                                       TheAdmin),
                              TheAdmin             => null),
          --  Refined_Pre     => not EnrolmentIsInProgress and then
          --                       ((Status = WaitingStartAdminOp or else
          --                           Status = WaitingFinishAdminOp) <=
          --                          (Admin.IsDoingOp(TheAdmin) and then
          --                             Admin.IsPresent(TheAdmin))),
          Refined_Post    =>  not EnrolmentIsInProgress and
                              Admin.RolePresent(TheAdmin) =
                                PrivTypes.UserOnly and
                              not Admin.IsDoingOp(TheAdmin) and
                              (Status = EnclaveQuiescent or
                                 Status = WaitingRemoveAdminTokenFail or
                                 Status = Status'Old) and
                              not (Status = WaitingStartAdminOp or
                                     Status = WaitingFinishAdminOp)
   is
   begin
      if PresentAdminHasDeparted(TheAdmin) then
         if Status = EnclaveQuiescent then

            -- TokenRemovedAdminLogoutC actions
            AuditLog.AddElementToLog
              (ElementID   => AuditTypes.AdminTokenRemoved,
               Severity    => AuditTypes.Information,
               User        => AdminToken.ExtractUser,
               Description => AuditTypes.NoDescription);

            AdminTokenTear;

         elsif Status = WaitingStartAdminOp or
           Status = WaitingFinishAdminOp
         then

            -- BadAdminLogoutC
            BadAdminTokenTear;

         end if;
      else -- AdminTokenHasExpired

         -- AdminTokenTimeoutC actions
         AuditLog.AddElementToLog
           (ElementID   => AuditTypes.AdminTokenExpired,
            Severity    => AuditTypes.Warning,
            User        => AdminToken.ExtractUser,
            Description => AuditTypes.NoDescription);

         Status := WaitingRemoveAdminTokenFail;

      end if;

      Admin.Logout(TheAdmin => TheAdmin);

   end AdminLogout;

   ------------------------------------------------------------------
   -- ProgressAdminActivity
   --
   -- Implementation Notes:
   --    None
   ------------------------------------------------------------------
   procedure ProgressAdminActivity (TheAdmin : in out Admin.T)
     with Refined_Global  => (Input  => (AdminToken.Input,
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
                                         Status,
                                         UserToken.State)),
          Refined_Depends => ((AdminToken.State,
                               TheAdmin)             => (AdminToken.Input,
                                                         AdminToken.State,
                                                         AdminToken.Status,
                                                         Clock.CurrentTime,
                                                         Door.State,
                                                         KeyStore.State,
                                                         KeyStore.Store,
                                                         Status,
                                                         TheAdmin),
                              AdminToken.Status      =>+ (AdminToken.State,
                                                          Status),
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
                                                         Status,
                                                         TheAdmin),
                              (ConfigData.FileState,
                               ConfigData.State)     =>+ (Floppy.State,
                                                          Status,
                                                          TheAdmin),
                              (Display.State,
                               UserToken.State)      =>+ (Door.State,
                                                          Status,
                                                          TheAdmin),
                              (Door.State,
                               Latch.State)          => (Clock.CurrentTime,
                                                         ConfigData.State,
                                                         Door.State,
                                                         Latch.State,
                                                         Status,
                                                         TheAdmin),
                              Floppy.Output          =>+ (AuditLog.FileState,
                                                          AuditLog.State,
                                                          Floppy.State,
                                                          Status,
                                                          TheAdmin),
                              Floppy.State           =>+ (Floppy.Input,
                                                          Status,
                                                          TheAdmin),
                              Floppy.WrittenState    =>+ (AuditLog.FileState,
                                                          AuditLog.State,
                                                          Floppy.State,
                                                          Status,
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
                                                          Status, TheAdmin),
                              Status                 =>+ (AdminToken.Input,
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
     --       Refined_Pre     =>
     --  not EnrolmentIsInProgress and then
     --    CurrentAdminActivityPossible and then

     --    ( ( Latch.IsLocked and then
     --          Door.TheCurrentDoor = Door.Open and then
     --          Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
     --                                   Door.Alarm_Timeout) ) =
     --        (Door.TheDoorAlarm = AlarmTypes.Alarming) ) and then

     --    ( ( Status = GotAdminToken or else
     --          Status = WaitingRemoveAdminTokenFail ) <=
     --        (not Admin.IsPresent(TheAdmin)) ) and then

     --    ( (not Admin.IsPresent(TheAdmin)) <= (not Admin.IsDoingOp(TheAdmin)) )
     --    and then

     --    ( ( Status = WaitingStartAdminOp or else
     --          Status = WaitingFinishAdminOp ) <=
     --        ( Admin.IsPresent(TheAdmin) and then
     --            Admin.IsDoingOp(TheAdmin) ) ) and then

     --    ( (Status = EnclaveQuiescent) <=
     --        (not Admin.IsDoingOp(TheAdmin)) ) and then

     --    ( (Status = Shutdown) <=
     --        ( not Admin.IsDoingOp(TheAdmin) and then
     --            Admin.RolePresent(TheAdmin) = PrivTypes.UserOnly ) ) and then

     --    ( ( Admin.IsDoingOp(TheAdmin) and then
     --          Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp ) <=
     --        (Status = WaitingStartAdminOp) ) and then

     --    ( (Admin.RolePresent(TheAdmin) = PrivTypes.Guard) <=
     --        ( AdminToken.IsGood and then
     --            AdminToken.AuthCertValid and then
     --            AdminToken.TheAuthCertRole = PrivTypes.Guard )) and then

     --    ( ( Admin.IsDoingOp(TheAdmin) and then
     --          Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) <=
     --        (Admin.RolePresent(TheAdmin) = PrivTypes.Guard) ) and then

     --    ( (Admin.RolePresent(TheAdmin) = PrivTypes.Guard) <=
     --        ( ( Admin.IsDoingOp(TheAdmin) and then
     --              Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) or else
     --            not Admin.IsDoingOp(TheAdmin) )),

          --------------------------------------------------------
          -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
          --====================================================--
          -- After each call to ProgressAdminActivity, the      --
          -- security property holds.                           --
          --------------------------------------------------------
          Refined_Post    =>
     not EnrolmentIsInProgress and

     ((Latch.IsLocked and
         Door.TheCurrentDoor = Door.Open and
         Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
                                  Door.Alarm_Timeout)) =
        (Door.TheDoorAlarm = AlarmTypes.Alarming)) and

     (if Admin.RolePresent(TheAdmin) = PrivTypes.Guard then
         (AdminToken.IsGood and
            AdminToken.AuthCertValid and
            AdminToken.TheAuthCertRole = PrivTypes.Guard)) and

     (if (not Latch.IsLocked and Latch.IsLocked'Old) then
         ((AdminToken.IsGood and
             AdminToken.AuthCertValid and
             AdminToken.TheAuthCertRole = PrivTypes.Guard))) and

     (if (Admin.IsDoingOp(TheAdmin) and then
            Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock)
      then
          Admin.RolePresent(TheAdmin) = PrivTypes.Guard) and

     (if Admin.RolePresent(TheAdmin) = PrivTypes.Guard then
         ((Admin.IsDoingOp(TheAdmin) and then
             Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock) or
            not Admin.IsDoingOp(TheAdmin))) and

     (if not Admin.IsPresent(TheAdmin) then not Admin.IsDoingOp(TheAdmin)) and

     (if (Status = GotAdminToken or
            Status = WaitingRemoveAdminTokenFail)
      then
          not Admin.IsPresent(TheAdmin)) and

     (if (Status = WaitingStartAdminOp or
            Status = WaitingFinishAdminOp)
      then
          (Admin.IsDoingOp(TheAdmin) and
             Admin.IsPresent(TheAdmin) and
             Admin.RolePresent(TheAdmin) = Admin.RolePresent(TheAdmin'Old)))
       and

     (if Status = EnclaveQuiescent then not Admin.IsDoingOp(TheAdmin)) and

     (if Status = Shutdown then
         (not Admin.IsDoingOp(TheAdmin) and
            Admin.RolePresent(TheAdmin) = PrivTypes.UserOnly)) and

     (if (Admin.IsDoingOp(TheAdmin) and then
            Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp)
      then
          Status = WaitingStartAdminOp) and

     (if (not Latch.IsLocked and Latch.IsLocked'Old) then
         (Admin.IsDoingOp(TheAdmin'Old) and
            Admin.TheCurrentOp(TheAdmin'Old) = Admin.OverrideLock))
   is
      LocalStatus : NonQuiescentStates;
   begin
      LocalStatus := NonQuiescentStates'(Status);

      case LocalStatus is
         -- TISProgressAdminLogon
         when GotAdminToken =>
            ValidateAdminToken (TheAdmin => TheAdmin);
         when WaitingRemoveAdminTokenFail =>
            CompleteFailedAdminLogon;
         -- TISAdminOp
         when WaitingStartAdminOp | WaitingFinishAdminOp =>
            AdminOp(TheAdmin => TheAdmin);
         when Shutdown =>
            null;
      end case;

   end ProgressAdminActivity;

   ------------------------------------------------------------------
   -- StartAdminActivity
   --
   -- Implementation Notes:
   --    When attempting to logon an administrator, the physical reading
   --    of the certificates from the token is postponed until validation
   --    since only as many certificates as are required to do this
   --    validation are read from the token.
   --
   ------------------------------------------------------------------
   procedure StartAdminActivity (TheAdmin : in out Admin.T)
     with Refined_Global  => (Input  => (AdminToken.State,
                                         Clock.Now,
                                         ConfigData.State,
                                         Keyboard.Inputs),
                              In_Out => (AuditLog.FileState,
                                         AuditLog.State,
                                         Screen.State,
                                         Status)),
          Refined_Depends => ((AuditLog.FileState,
                               AuditLog.State)     => (AdminToken.State,
                                                       AuditLog.FileState,
                                                       AuditLog.State,
                                                       Clock.Now,
                                                       ConfigData.State,
                                                       Keyboard.Inputs,
                                                       Screen.State,
                                                       Status,
                                                       TheAdmin),
                              (Screen.State,
                               Status,
                               TheAdmin)           =>+ (AdminToken.State,
                                                        Keyboard.Inputs,
                                                        Status,
                                                        TheAdmin)),
     --       Refined_Pre     => ,
     --  not EnrolmentIsInProgress and then

     --  ( (Admin.RolePresent(TheAdmin) = PrivTypes.Guard) <=
     --      ( AdminToken.IsGood and then
     --          AdminToken.AuthCertValid and then
     --          AdminToken.TheAuthCertRole = PrivTypes.Guard ))
     --  and then

     --  ( (not Admin.IsPresent(TheAdmin)) <=
     --      (not Admin.IsDoingOp(TheAdmin)) ) and then

     --  ( ( Status = GotAdminToken or else
     --        Status = WaitingRemoveAdminTokenFail ) <=
     --      (not Admin.IsPresent(TheAdmin)) ) and then

     --  ( ( Status = WaitingStartAdminOp or else
     --        Status = WaitingFinishAdminOp ) <=
     --      ( Admin.IsPresent(TheAdmin) and then
     --          Admin.IsDoingOp(TheAdmin) ) ) and then

     --  ( (Status = EnclaveQuiescent) <=
     --      (not Admin.IsDoingOp(TheAdmin)) ) and then

     --  ( (Status = Shutdown) <=
     --      ( not Admin.IsDoingOp(TheAdmin) and then
     --          Admin.RolePresent(TheAdmin) = PrivTypes.UserOnly ) ) and then

     --  ( ( Admin.IsDoingOp(TheAdmin) and then
     --        Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) <=
     --      (Admin.RolePresent(TheAdmin) = PrivTypes.Guard) ) and then

     --  ( ( Admin.IsDoingOp(TheAdmin) and then
     --        Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp ) <=
     --      (Status = WaitingStartAdminOp) ) and then

     --  ( (Admin.RolePresent(TheAdmin) = PrivTypes.Guard) <=
     --      ( ( Admin.IsDoingOp(TheAdmin) and then
     --            Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) or else
     --          not Admin.IsDoingOp(TheAdmin) ))
          Refined_Post    =>
     not EnrolmentIsInProgress and

     (if not Admin.IsPresent(TheAdmin) then
         not Admin.IsDoingOp(TheAdmin)) and

     (if (Status = GotAdminToken or
            Status = WaitingRemoveAdminTokenFail)
      then
          not Admin.IsPresent(TheAdmin)) and

     (if (Status = WaitingStartAdminOp or
            Status = WaitingFinishAdminOp)
      then
         (Admin.IsDoingOp(TheAdmin) and
            Admin.IsPresent(TheAdmin) and
            Admin.RolePresent(TheAdmin) = Admin.RolePresent(TheAdmin'Old)))
       and

     (if Status = EnclaveQuiescent then
         (not Admin.IsDoingOp(TheAdmin) and
            Admin.RolePresent(TheAdmin) = Admin.RolePresent(TheAdmin'Old)))
       and

     (if Status = Shutdown then
         (not Admin.IsDoingOp(TheAdmin) and
            Admin.RolePresent(TheAdmin) = PrivTypes.UserOnly)) and

     (if (Admin.IsDoingOp(TheAdmin) and then
            Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp)
      then
          Status = WaitingStartAdminOp) and

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
            not Admin.IsDoingOp(TheAdmin)))
   is
      ------------------------------------------------------------------
      -- AdminLogonCanStart
      --
      -- Description:
      --    Returns True exactly when there is no administrator
      --    logged on and the enclave is quiescent, but an administrator
      --    token is present.
      --
      -- Implementation Notes:
      --    None.
      --
      -- Traceunit : C.Enclave.AdminLogonCanStart
      -- Traceto   : FD.Enclave.AdminLogonCanStart
      ------------------------------------------------------------------
      function AdminLogonCanStart return Boolean is
        (not Admin.IsPresent(TheAdmin)
           and Status = EnclaveQuiescent
           and AdminToken.IsPresent)
        with Global => (AdminToken.State,
                        Status,
                        TheAdmin);

      ------------------------------------------------------------------
      -- AdminOpCanStart
      --
      -- Description:
      --    Returns True exactly when a logged on administrator's
      --    token is present and the enclave is quiescent.
      --
      -- Implementation Notes:
      --    None.
      --
      -- Traceunit : C.Enclave.AdminOpCanStart
      -- Traceto   : FD.Enclave.AdminOpCanStart
      ------------------------------------------------------------------
      function AdminOpCanStart return Boolean is
        (Admin.IsPresent(TheAdmin)
           and Status = EnclaveQuiescent
           and AdminToken.IsPresent)
        with Global  => (AdminToken.State,
                         Status,
                         TheAdmin);

      ------------------------------------------------------------------
      -- StartAdminOp
      --
      -- Description:
      --    Checks whether the administrator has requested a (valid)
      --    operation via the keyboard.
      --
      -- Implementation Notes:
      --    None
      --
      -- Traceunit : C.Enclave.StartAdminOp
      -- Traceto   : FD.Enclave.TISStartAdminOpC
      ------------------------------------------------------------------
      procedure StartAdminOp
        with Global  => (Input  => (AdminToken.State,
                                    Clock.Now,
                                    ConfigData.State,
                                    Keyboard.Inputs),
                         In_Out => (AuditLog.FileState,
                                    AuditLog.State,
                                    Screen.State,
                                    Status,
                                    TheAdmin)),
             Depends => ((AuditLog.FileState,
                          AuditLog.State)     => (AdminToken.State,
                                                  AuditLog.FileState,
                                                  AuditLog.State,
                                                  Clock.Now,
                                                  ConfigData.State,
                                                  Keyboard.Inputs,
                                                  Screen.State,
                                                  TheAdmin),
                         (Screen.State,
                          Status,
                          TheAdmin)           =>+ (Keyboard.Inputs,
                                                   TheAdmin)),
             Pre     =>
        AdminOpCanStart and
        Status = EnclaveQuiescent and

        Admin.IsPresent(TheAdmin) and
        not Admin.IsDoingOp(TheAdmin) and

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
             Post    =>
        (Status = EnclaveQuiescent or
           Status = WaitingStartAdminOp) and

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

        (if (Admin.IsDoingOp(TheAdmin) and then
               Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp)
         then
            Status = WaitingStartAdminOp) and

        (if (Status = WaitingStartAdminOp or
               Status = WaitingFinishAdminOp)
         then
             (Admin.IsDoingOp(TheAdmin) and
                Admin.IsPresent(TheAdmin) and
                Admin.RolePresent(TheAdmin) =
                Admin.RolePresent(TheAdmin'Old))) and

        (if Status = EnclaveQuiescent then
            (not Admin.IsDoingOp(TheAdmin) and
               Admin.RolePresent(TheAdmin) =
               Admin.RolePresent(TheAdmin'Old))) and

        (if Status = Shutdown then
            (not Admin.IsDoingOp(TheAdmin) and
               Admin.RolePresent(TheAdmin) = PrivTypes.UserOnly))
      is
         KeyedDataPresence : CommonTypes.PresenceT;
         KeyedData         : Keyboard.DataT;
         TheOp             : Admin.OpAndNullT;
      begin
         Keyboard.Read(DataPresence => KeyedDataPresence,
                       Data         => KeyedData);

         if KeyedDataPresence = CommonTypes.Present then
            TheOp := Admin.OpIsAvailable(TheAdmin => TheAdmin,
                                         KeyedOp  => KeyedData);

            if TheOp /= Admin.NullOp then

               -- ValidateOpRequestOK actions
               Status := WaitingStartAdminOp;

               Screen.SetMessage(Msg => Screen.DoingOp);
               Admin.StartOp(TheAdmin => TheAdmin,
                             Op       => TheOp);

               AuditLog.AddElementToLog
                 (ElementID   => AuditTypes.OperationStart,
                  Severity    => AuditTypes.Information,
                  User        => AdminToken.ExtractUser,
                  Description => KeyedData.Text);
            else

               -- ValidateOpRequestFail actions
               Screen.SetMessage(Msg => Screen.InvalidRequest);

               AuditLog.AddElementToLog
                 (ElementID   => AuditTypes.InvalidOpRequest,
                  Severity    => AuditTypes.Warning,
                  User        => AdminToken.ExtractUser,
                  Description => KeyedData.Text);
            end if;
         end if; -- NoOpRequest

      end StartAdminOp;

   ------------------------------------------------------------------
   -- begin StartAdminActivity
   ------------------------------------------------------------------
   begin
      if AdminLogonCanStart then
         Status := GotAdminToken;
      elsif AdminOpCanStart then
         StartAdminOp;
      end if;
   end StartAdminActivity;

   ------------------------------------------------------------------
   -- ResetScreenMessage
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure ResetScreenMessage (TheAdmin : in Admin.T)
     with Refined_Global  => (Input  => (Clock.Now,
                                         ConfigData.State,
                                         Status),
                              In_Out => (AuditLog.FileState,
                                         AuditLog.State,
                                         Screen.State)),
          Refined_Depends => ((AuditLog.FileState,
                               AuditLog.State)     => (AuditLog.FileState,
                                                       AuditLog.State,
                                                       Clock.Now,
                                                       ConfigData.State,
                                                       Screen.State,
                                                       Status,
                                                       TheAdmin),
                              Screen.State         =>+ (Status,
                                                        TheAdmin))
   is
   begin
      if Status = EnclaveQuiescent then
         if Admin.IsPresent(TheAdmin => TheAdmin) then
            Screen.SetMessage(Msg => Screen.RequestAdminOp);
         else
            Screen.SetMessage(Msg => Screen.WelcomeAdmin);
         end if;
      elsif Status = WaitingRemoveAdminTokenFail then
         Screen.SetMessage(Msg => Screen.RemoveAdminToken);
      end if;

   end ResetScreenMessage;

end Enclave;
