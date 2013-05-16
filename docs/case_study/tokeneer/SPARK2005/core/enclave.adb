------------------------------------------------------------------
-- Tokeneer ID Station Core Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency. All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd. under contract to the National Security Agency.
--
-- Modifications to proof annotations by Phil Thornley, April 2009
------------------------------------------------------------------

------------------------------------------------------------------
-- Enclave
--
-- Implementation Notes:
--    None.
--
------------------------------------------------------------------
with Admin,
     AdminToken,
     AuditLog,
     AuditTypes,
     BasicTypes,
     Configuration,
     Door,
     Display,
     Enrolment,
     File,
     Floppy,
     KeyStore,
     Keyboard,
     Latch,
     Screen,
     UserToken;

use type Admin.OpAndNullT;
use type BasicTypes.PresenceT;
use type Door.T;

package body Enclave
--# own State is Status;
is

   ------------------------------------------------------------------
   --  Types
   ------------------------------------------------------------------
   type StatusT is (NotEnrolled,
                    WaitingEnrol,
                    WaitingEndEnrol,
                    EnclaveQuiescent,
                    WaitingRemoveAdminTokenFail,
                    GotAdminToken,
                    WaitingStartAdminOp,
                    WaitingFinishAdminOp,
                    ShutDown);

   subtype EnrolmentStates is StatusT
     range NotEnrolled .. WaitingEndEnrol;

   subtype ActiveEnclaveStates is StatusT
     range GotAdminToken .. Shutdown;

   subtype NonQuiescentStates is StatusT
     range WaitingRemoveAdminTokenFail .. Shutdown;
   ------------------------------------------------------------------
   --  State
   ------------------------------------------------------------------
   Status : StatusT;


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
     --# global AdminToken.State;
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
   function AdminTokenHasExpired (TheAdmin : Admin.T) return Boolean
     --# global AdminToken.State,
     --#        Status,
     --#        Clock.CurrentTime;
   is
   begin
      return ( Admin.IsPresent(TheAdmin)
               and AdminToken.IsPresent
               and Status = EnclaveQuiescent
               and not AdminToken.IsCurrent );
   end AdminTokenHasExpired;


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
   function AdminHasDeparted return Boolean
     --# global AdminToken.State,
     --#        Status;
   --# return R => (R -> Status in NonQuiescentStates);
   is
   begin
      return ( not AdminToken.IsPresent
               and Status in NonQuiescentStates );
   end AdminHasDeparted;


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
   --# global in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in     Floppy.Input;
   --#        in out Status;
   --#        in out Screen.State;
   --#        in out Display.State;
   --#        in out Floppy.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --# derives Status,
   --#         Screen.State,
   --#         Display.State      from *,
   --#                                 Floppy.State &
   --#         AuditLog.State,
   --#         AuditLog.FileState from Screen.State,
   --#                                 Display.State,
   --#                                 Floppy.State,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 ConfigData.State,
   --#                                 Clock.Now &
   --#         Floppy.State       from *,
   --#                                 Floppy.Input;
   --# pre Status in EnrolmentStates;
   --# post Status in EnrolmentStates;
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
   --# global in     Floppy.State;
   --#        in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in out Screen.State;
   --#        in out Display.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#        in out KeyStore.Store;
   --#        in out KeyStore.State;
   --#           out Status;
   --# derives Status,
   --#         KeyStore.Store     from Floppy.State,
   --#                                 KeyStore.Store &
   --#         Screen.State,
   --#         Display.State,
   --#         KeyStore.State     from *,
   --#                                 Floppy.State,
   --#                                 KeyStore.Store &
   --#         AuditLog.State,
   --#         AuditLog.FileState from Screen.State,
   --#                                 Display.State,
   --#                                 Floppy.State,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 ConfigData.State,
   --#                                 Clock.Now,
   --#                                 KeyStore.Store;
   --# pre not KeyStore.PrivateKeyPresent(KeyStore.State);
   --# post (Status = EnclaveQuiescent and
   --#       KeyStore.PrivateKeyPresent(KeyStore.State)) or
   --#      (Status = WaitingEndEnrol and
   --#       not KeyStore.PrivateKeyPresent(KeyStore.State));
   is
      TheCurrentFloppy : File.T;
      DataOK : Boolean;
      Description : AuditTypes.DescriptionT;
   begin
      TheCurrentFloppy := Floppy.CurrentFloppy;

      --# accept F, 10, TheCurrentFloppy, "Ineffective assignment expected here";
      Enrolment.Validate(TheFile     => TheCurrentFloppy,
                         DataOK      => DataOK,
                         Description => Description);
      --# end accept;

      if DataOK then

         -- ValidateEnrolmentDataOK actions
         Screen.SetMessage(Msg => Screen.WelcomeAdmin);
         Display.SetValue(Msg => Display.Welcome);
         Status := EnclaveQuiescent;

         AuditLog.AddElementToLog
           ( ElementID   => AuditTypes.EnrolmentComplete,
             Severity    => AuditTypes.Information,
             User        => AuditTypes.NoUser,
             Description => AuditTypes.NoDescription
             );

      else
         -- ValidateEnrolmentDataFail actions
         Screen.SetMessage(Msg => Screen.EnrolmentFailed);
         Display.SetValue(Msg => Display.Blank);
         Status := WaitingEndEnrol;

         AuditLog.AddElementToLog
           ( ElementID   => AuditTypes.EnrolmentFailed,
             Severity    => AuditTypes.Warning,
             User        => AuditTypes.NoUser,
             Description => Description
             );

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
   --# global in     Floppy.State;
   --#        in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in out Status;
   --#        in out Screen.State;
   --#        in out Display.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --# derives Status,
   --#         Screen.State,
   --#         Display.State      from *,
   --#                                 Floppy.State &
   --#         AuditLog.State,
   --#         AuditLog.FileState from Screen.State,
   --#                                 Display.State,
   --#                                 Floppy.State,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 ConfigData.State,
   --#                                 Clock.Now;
   --# pre Status = WaitingEndEnrol;
   --# post Status = WaitingEndEnrol or Status = NotEnrolled;
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
   --# global in out AdminToken.State;
   --# derives AdminToken.State   from * ;
--    --# post not AdminToken.prf_isGood(AdminToken.State) and
--    --#      not AdminToken.prf_authCertValid(AdminToken.State) and
--    --#      not ( AdminToken.TheAuthCertRole(AdminToken.State)
--    --#               in PrivTypes.AdminPrivilegeT );
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
   --# global in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in out AdminToken.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#           out Status;
   --# derives AdminToken.State   from * &
   --#         AuditLog.State,
   --#         AuditLog.FileState from AdminToken.State,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 ConfigData.State,
   --#                                 Clock.Now &
   --#         Status             from ;
   --# post Status = EnclaveQuiescent;
--    --#      not AdminToken.prf_isGood(AdminToken.State) and
--    --#      not AdminToken.prf_authCertValid(AdminToken.State) and
--    --#      not ( AdminToken.TheAuthCertRole(AdminToken.State)
--    --#               in PrivTypes.AdminPrivilegeT );
   is
   begin

      AuditLog.AddElementToLog
        ( ElementID   => AuditTypes.AdminTokenRemoved,
          Severity    => AuditTypes.Warning,
          User        => AdminToken.ExtractUser,
          Description => AuditTypes.NoDescription
          );

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
   --# global in     Clock.CurrentTime;
   --#        in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in     KeyStore.Store;
   --#        in     KeyStore.State;
   --#        in     AdminToken.Input;
   --#        in out AdminToken.State;
   --#        in out Screen.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#        in out AdminToken.Status;
   --#           out Status;
   --# derives AdminToken.State,
   --#         Screen.State,
   --#         TheAdmin           from *,
   --#                                 AdminToken.State,
   --#                                 Clock.CurrentTime,
   --#                                 KeyStore.Store,
   --#                                 KeyStore.State,
   --#                                 AdminToken.Status,
   --#                                 AdminToken.Input &
   --#         AuditLog.State,
   --#         AuditLog.FileState from AdminToken.State,
   --#                                 Clock.CurrentTime,
   --#                                 Screen.State,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 ConfigData.State,
   --#                                 Clock.Now,
   --#                                 KeyStore.Store,
   --#                                 KeyStore.State,
   --#                                 AdminToken.Status,
   --#                                 AdminToken.Input &
   --#         Status             from AdminToken.State,
   --#                                 Clock.CurrentTime,
   --#                                 KeyStore.Store,
   --#                                 KeyStore.State,
   --#                                 AdminToken.Status,
   --#                                 AdminToken.Input &
   --#         AdminToken.Status  from *,
   --#                                 AdminToken.State;
   --#
   --# pre not Admin.IsPresent(TheAdmin) and
   --#     not Admin.IsDoingOp(TheAdmin) and
   --#
   --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
   --#           ( AdminToken.prf_isGood(AdminToken.State) and
   --#             AdminToken.prf_authCertValid(AdminToken.State) and
   --#             AdminToken.TheAuthCertRole(AdminToken.State) = PrivTypes.Guard )) and
   --#
   --#      ( ( Admin.IsDoingOp(TheAdmin) and
   --#          Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) ->
   --#           Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ) and
   --#
   --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
   --#           ( ( Admin.IsDoingOp(TheAdmin) and
   --#               Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) or
   --#             not Admin.IsDoingOp(TheAdmin) ));
   --#
   --#
   --# post ( Status = EnclaveQuiescent or
   --#        Status = WaitingRemoveAdminTokenFail ) and
   --#
   --#      ( Status = WaitingRemoveAdminTokenFail -> not Admin.IsPresent(TheAdmin) ) and
   --#
   --#      not Admin.IsDoingOp(TheAdmin) and
   --#
   --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
   --#           ( AdminToken.prf_isGood(AdminToken.State) and
   --#             AdminToken.prf_authCertValid(AdminToken.State) and
   --#             AdminToken.TheAuthCertRole(AdminToken.State) = PrivTypes.Guard )) and
   --#
   --#      ( ( Admin.IsDoingOp(TheAdmin) and
   --#          Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) ->
   --#           Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ) and
   --#
   --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
   --#           ( ( Admin.IsDoingOp(TheAdmin) and
   --#               Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) or
   --#             not Admin.IsDoingOp(TheAdmin) ));
   is

     TokenOK : Boolean;

     Description : AuditTypes.DescriptionT;
   begin

      if not AdminToken.IsPresent then

         -- LoginAbortedC actions
         BadAdminTokenTear;

         --# check Admin.prf_rolePresent(TheAdmin) /= PrivTypes.Guard;

      else

         AdminToken.ReadAndCheck (Description => Description,
                                  TokenOK     => TokenOk);

         -- GetPresentAdminTokenC postponed actions
         AuditLog.AddElementToLog
           ( ElementID   => AuditTypes.AdminTokenPresent,
             Severity    => AuditTypes.Information,
             User        => AdminToken.ExtractUser,
             Description => AuditTypes.NoDescription
             );

         if TokenOK then

            -- ValidateAdminTokenOKC actions
            AuditLog.AddElementToLog
              ( ElementID   => AuditTypes.AdminTokenValid,
                Severity    => AuditTypes.Information,
                User        => AdminToken.ExtractUser,
                Description => AuditTypes.NoDescription
                );

            Screen.SetMessage (Msg => Screen.RequestAdminOp);
            Status := EnclaveQuiescent;

            Admin.Logon (TheAdmin => TheAdmin,
                         Role     => AdminToken.GetRole);

            --# check AdminToken.GetRole (AdminToken.State) = PrivTypes.Guard ->
            --#         AdminToken.TheAuthCertRole (AdminToken.State) = PrivTypes.Guard;

         else

            -- ValidateAdminTokenFailC actions

            AuditLog.AddElementToLog
              ( ElementID   => AuditTypes.AdminTokenInvalid,
                Severity    => AuditTypes.Warning,
                User        => AdminToken.ExtractUser,
                Description => Description
                );

            Screen.SetMessage (Msg => Screen.RemoveAdminToken);
            Status := WaitingRemoveAdminTokenFail;


            --# check Admin.prf_rolePresent(TheAdmin) /= PrivTypes.Guard;

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
   --# global in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in out AdminToken.State;
   --#        in out Screen.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#           out Status;
   --# derives AdminToken.State,
   --#         Screen.State       from * &
   --#         AuditLog.State,
   --#         AuditLog.FileState from AdminToken.State,
   --#                                 Screen.State,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 ConfigData.State,
   --#                                 Clock.Now &
   --#         Status             from ;
   --# post Status = EnclaveQuiescent;
--    --#      not AdminToken.prf_isGood(AdminToken.State) and
--    --#      not AdminToken.prf_authCertValid(AdminToken.State) and
--    --#      AdminToken.TheAuthCertRole(AdminToken.State) /= PrivTypes.Guard;
   is

   begin

      AuditLog.AddElementToLog
        ( ElementID   => AuditTypes.AdminTokenRemoved,
          Severity    => AuditTypes.Information,
          User        => AdminToken.ExtractUser,
          Description => AuditTypes.NoDescription
          );

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
   --# global in     AdminToken.State;
   --#        in     Clock.Now;
   --#           out Floppy.Output;
   --#        in out Status;
   --#        in out Screen.State;
   --#        in out Floppy.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#        in     ConfigData.State;
   --#        in out Floppy.WrittenState;
   --#        in     Floppy.Input;
   --# derives Status               from *, Floppy.State &
   --#         Screen.State         from *,
   --#                                   Status,
   --#                                   Floppy.State,
   --#                                   Floppy.Input,
   --#                                   Floppy.WrittenState &
   --#         AuditLog.State,
   --#         AuditLog.FileState   from AdminToken.State,
   --#                                   Screen.State, Status,
   --#                                   Floppy.State,
   --#                                   Floppy.WrittenState,
   --#                                   Floppy.Input,
   --#                                   AuditLog.State,
   --#                                   AuditLog.FileState,
   --#                                   ConfigData.State,
   --#                                   Clock.Now &
   --#         Floppy.Output        from Floppy.State, Status,
   --#                                   AuditLog.State,
   --#                                   AuditLog.FileState &
   --#         Floppy.State         from *, Status &
   --#         Floppy.WrittenState  from *, Floppy.State, Status,
   --#                                   AuditLog.State,
   --#                                   AuditLog.FileState &
   --#         TheAdmin             from *, Status ;
   --#
   --# pre  ( Status = WaitingStartAdminOp or
   --#        Status = WaitingFinishAdminOp ) and
   --#
   --#      Admin.IsPresent(TheAdmin) and
   --#      Admin.IsDoingOp(TheAdmin) and
   --#      Admin.TheCurrentOp(TheAdmin) = Admin.ArchiveLog and
   --#
   --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
   --#           ( AdminToken.prf_isGood(AdminToken.State) and
   --#             AdminToken.prf_authCertValid(AdminToken.State) and
   --#             AdminToken.TheAuthCertRole(AdminToken.State) = PrivTypes.Guard )) and
   --#
   --#      ( ( Admin.IsDoingOp(TheAdmin) and
   --#          Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) ->
   --#           Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ) and
   --#
   --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
   --#           ( ( Admin.IsDoingOp(TheAdmin) and
   --#               Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) or
   --#             not Admin.IsDoingOp(TheAdmin) ));
   --#
   --#
   --# post ( Status = WaitingStartAdminOp or
   --#        Status = WaitingFinishAdminOp or
   --#        Status = EnclaveQuiescent ) and
   --#
   --#      Admin.IsPresent(TheAdmin) and
   --#
   --#      ( ( Status = WaitingStartAdminOp or
   --#          Status = WaitingFinishAdminOp ) ->
   --#        ( Admin.IsDoingOp(TheAdmin) and
   --#          Admin.IsPresent(TheAdmin) and
   --#          Admin.TheCurrentOp(TheAdmin) = Admin.ArchiveLog ) ) and
   --#
   --#      ( Status = EnclaveQuiescent ->
   --#        not Admin.IsDoingOp(TheAdmin) ) and
   --#
   --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
   --#           ( AdminToken.prf_isGood(AdminToken.State) and
   --#             AdminToken.prf_authCertValid(AdminToken.State) and
   --#             AdminToken.TheAuthCertRole(AdminToken.State) = PrivTypes.Guard )) and
   --#
   --#      ( ( Admin.IsDoingOp(TheAdmin) and
   --#          Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) ->
   --#           Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ) and
   --#
   --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
   --#           ( ( Admin.IsDoingOp(TheAdmin) and
   --#               Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) or
   --#             not Admin.IsDoingOp(TheAdmin) )) and
   --#
   --#      Admin.prf_rolePresent(TheAdmin) = Admin.prf_rolePresent(TheAdmin~);
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
      --# global in     AdminToken.State;
      --#        in     Clock.Now;
      --#           out Floppy.Output;
      --#        in out Status;
      --#        in out Screen.State;
      --#        in out Floppy.State;
      --#        in out AuditLog.State;
      --#        in out AuditLog.FileState;
      --#        in     ConfigData.State;
      --#        in out Floppy.WrittenState;
      --# derives Status               from *, Floppy.State &
      --#         Screen.State         from *,
      --#                                   Floppy.State &
      --#         AuditLog.State,
      --#         AuditLog.FileState   from AdminToken.State,
      --#                                   Screen.State,
      --#                                   Floppy.State,
      --#                                   AuditLog.State,
      --#                                   AuditLog.FileState,
      --#                                   ConfigData.State,
      --#                                   Clock.Now &
      --#         Floppy.State         from * &
      --#         Floppy.Output        from Floppy.State,
      --#                                   AuditLog.State,
      --#                                   AuditLog.FileState &
      --#         Floppy.WrittenState  from *, Floppy.State,
      --#                                   AuditLog.State,
      --#                                   AuditLog.FileState;
      --# pre Status = WaitingStartAdminOp;
      --# post Status = WaitingStartAdminOp or
      --#      Status = WaitingFinishAdminOp;
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
      --# global in     AdminToken.State;
      --#        in out TheAdmin;
      --#        in     Clock.Now;
      --#        in     Floppy.Input;
      --#        in out Floppy.WrittenState;
      --#           out Status;
      --#        in out Screen.State;
      --#        in out Floppy.State;
      --#        in out AuditLog.State;
      --#        in out AuditLog.FileState;
      --#        in     ConfigData.State;
      --# derives Status from &
      --#         Screen.State         from * ,
      --#                                   Floppy.State,
      --#                                   Floppy.WrittenState,
      --#                                   Floppy.Input &
      --#         AuditLog.State,
      --#         AuditLog.FileState   from AdminToken.State,
      --#                                   Screen.State,
      --#                                   Floppy.State,
      --#                                   Floppy.WrittenState,
      --#                                   Floppy.Input,
      --#                                   AuditLog.State,
      --#                                   AuditLog.FileState,
      --#                                   ConfigData.State,
      --#                                   Clock.Now &
      --#         Floppy.State         from * &
      --#         Floppy.WrittenState  from Floppy.State,
      --#                                   Floppy.WrittenState &
      --#         TheAdmin             from * ;
      --# pre Admin.IsPresent(TheAdmin);
      --# post Status = EnclaveQuiescent and
      --#      Admin.IsPresent(TheAdmin) and
      --#      not Admin.IsDoingOp(TheAdmin) and
      --#      Admin.prf_rolePresent(TheAdmin) = Admin.prf_rolePresent(TheAdmin~);
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
                 ( ElementID   => AuditTypes.ArchiveCheckFailed,
                   Severity    => AuditTypes.Warning,
                   User        => AdminToken.ExtractUser,
                   Description => "Archive Cancelled - Floppy has bad data"
                   );

               Screen.SetMessage(Msg => Screen.ArchiveFailed);

            end if;

         else
            -- FinishArchiveLogNoFloppy unique actions
            AuditLog.CancelArchive;

            AuditLog.AddElementToLog
              ( ElementID   => AuditTypes.ArchiveCheckFailed,
                Severity    => AuditTypes.Warning,
                User        => AdminToken.ExtractUser,
                Description => "Archive Cancelled - Floppy has been removed"
                );

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
   procedure UpdateConfigDataOp(TheAdmin : in out Admin.T)
   --# global in     AdminToken.State;
   --#        in     Clock.Now;
   --#        in     Floppy.Input;
   --#        in out Status;
   --#        in out Screen.State;
   --#        in out Floppy.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#        in out ConfigData.State;
   --#        in out ConfigData.FileState;
   --# derives Status,
   --#         Screen.State,
   --#         ConfigData.FileState from *,
   --#                                   Status,
   --#                                   Floppy.State &
   --#         AuditLog.State,
   --#         AuditLog.FileState   from AdminToken.State,
   --#                                   Status,
   --#                                   Screen.State,
   --#                                   Floppy.State,
   --#                                   AuditLog.State,
   --#                                   AuditLog.FileState,
   --#                                   ConfigData.State,
   --#                                   Clock.Now,
   --#                                   ConfigData.FileState &
   --#         Floppy.State         from *,
   --#                                   Status,
   --#                                   Floppy.Input &
   --#         ConfigData.State     from *,
   --#                                   Status,
   --#                                   Floppy.State &
   --#         TheAdmin             from *,
   --#                                   Status;
   --# pre  ( Status = WaitingStartAdminOp or
   --#        Status = WaitingFinishAdminOp ) and
   --#      Admin.IsPresent(TheAdmin) and
   --#      Admin.IsDoingOp(TheAdmin) and
   --#      Admin.TheCurrentOp(TheAdmin) = Admin.UpdateConfigData;
   --# post ( Status = WaitingStartAdminOp or
   --#        Status = WaitingFinishAdminOp or
   --#        Status = EnclaveQuiescent ) and
   --#      Admin.IsPresent(TheAdmin) and
   --#      ( ( Status = WaitingStartAdminOp or
   --#          Status = WaitingFinishAdminOp ) ->
   --#        ( Admin.IsDoingOp(TheAdmin) and
   --#          Admin.IsPresent(TheAdmin) and
   --#          Admin.TheCurrentOp(TheAdmin) = Admin.UpdateConfigData ) ) and
   --#
   --#      ( Status = EnclaveQuiescent ->
   --#        not Admin.IsDoingOp(TheAdmin) ) and
   --#
   --#      Admin.prf_rolePresent(TheAdmin) = Admin.prf_rolePresent(TheAdmin~);
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

         --# accept F, 10, TheCurrentFloppy, "Ineffective assignment expected here";
         Configuration.UpdateData
           ( TheFile   => TheCurrentFloppy,
             DataValid => ConfigDataOK );
         --# end accept;

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
   procedure OverrideDoorLockOp(TheAdmin : in out Admin.T)
   --# global in     AdminToken.State;
   --#        in     Clock.CurrentTime;
   --#        in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in out Screen.State;
   --#        in out Display.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#        in out Door.State;
   --#        in out Latch.State;
   --#           out Status;
   --# derives Screen.State,
   --#         Display.State,
   --#         TheAdmin           from * &
   --#         AuditLog.State,
   --#         AuditLog.FileState from AdminToken.State,
   --#                                 Clock.CurrentTime,
   --#                                 Screen.State,
   --#                                 Display.State,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 ConfigData.State,
   --#                                 Clock.Now,
   --#                                 Door.State,
   --#                                 Latch.State &
   --#         Door.State,
   --#         Latch.State        from *,
   --#                                 Clock.CurrentTime,
   --#                                 ConfigData.State,
   --#                                 Latch.State &
   --#         Status             from ;
   --# pre  Admin.IsDoingOp(TheAdmin) and
   --#      Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock and
   --#      Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard and
   --#
   --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
   --#           ( AdminToken.prf_isGood(AdminToken.State) and
   --#             AdminToken.prf_authCertValid(AdminToken.State) and
   --#             AdminToken.TheAuthCertRole(AdminToken.State) = PrivTypes.Guard )) and
   --#
   --#      ( ( Admin.IsDoingOp(TheAdmin) and
   --#          Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) ->
   --#           Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ) and
   --#
   --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
   --#           ( ( Admin.IsDoingOp(TheAdmin) and
   --#               Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) or
   --#             not Admin.IsDoingOp(TheAdmin) ) );
   --#
   --# post Status = EnclaveQuiescent and
   --#      --------------------------------------------------------
   --#      -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
   --#      --====================================================--
   --#      -- After each call to OverrideDoorLockOp, the         --
   --#      -- security property holds.                           --
   --#      --------------------------------------------------------
   --#      ( ( Latch.IsLocked(Latch.State) and
   --#          Door.TheCurrentDoor(Door.State) = Door.Open and
   --#          Clock.GreaterThanOrEqual(Clock.TheCurrentTime(Clock.CurrentTime),
   --#                                   Door.prf_alarmTimeout(Door.State)) ) <->
   --#        Door.TheDoorAlarm(Door.State) = AlarmTypes.Alarming ) and
   --#
   --#      Admin.prf_rolePresent(TheAdmin) = Admin.prf_rolePresent(TheAdmin~) and
   --#      not Admin.IsDoingOp(TheAdmin) and
   --#
   --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
   --#           ( AdminToken.prf_isGood(AdminToken.State) and
   --#             AdminToken.prf_authCertValid(AdminToken.State) and
   --#             AdminToken.TheAuthCertRole(AdminToken.State) = PrivTypes.Guard )) and
   --#
   --#      ( ( not Latch.IsLocked(Latch.State) and Latch.IsLocked(Latch.State~) )
   --#        ->
   --#        ( ( AdminToken.prf_isGood(AdminToken.State) and
   --#            AdminToken.prf_authCertValid(AdminToken.State) and
   --#            AdminToken.TheAuthCertRole(AdminToken.State) = PrivTypes.Guard )
   --#        )
   --#      ) and
   --#
   --#      ( ( Admin.IsDoingOp(TheAdmin) and
   --#          Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) ->
   --#           Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ) and
   --#
   --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
   --#           ( ( Admin.IsDoingOp(TheAdmin) and
   --#               Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) or
   --#             not Admin.IsDoingOp(TheAdmin) )) and
   --#
   --#      ( ( not Latch.IsLocked(Latch.State) and Latch.IsLocked(Latch.State~) )
   --#        -> ( Admin.IsDoingOp(TheAdmin~) and
   --#             Admin.TheCurrentOp(TheAdmin~) = Admin.OverrideLock ) );
   is
   begin
      AuditLog.AddElementToLog
        ( ElementID   => AuditTypes.OverrideLock,
          Severity    => AuditTypes.Information,
          User        => AdminToken.ExtractUser,
          Description => AuditTypes.NoDescription
          );

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
   --# global in     Clock.CurrentTime;
   --#        in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in out AdminToken.State;
   --#        in out Status;
   --#        in out Screen.State;
   --#        in out Display.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#        in out Door.State;
   --#        in out Latch.State;
   --#        in out UserToken.State;
   --# derives AdminToken.State,
   --#         Status,
   --#         Screen.State,
   --#         Display.State,
   --#         TheAdmin,
   --#         UserToken.State    from *,
   --#                                 Door.State &
   --#         AuditLog.State,
   --#         AuditLog.FileState from AdminToken.State,
   --#                                 Clock.CurrentTime,
   --#                                 Screen.State,
   --#                                 Display.State,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 ConfigData.State,
   --#                                 Clock.Now,
   --#                                 Door.State,
   --#                                 Latch.State &
   --#         Door.State,
   --#         Latch.State        from Clock.CurrentTime,
   --#                                 Door.State,
   --#                                 Latch.State;
   --# pre  Status = WaitingStartAdminOp and
   --#
   --#      Admin.IsPresent(TheAdmin) and
   --#      Admin.IsDoingOp(TheAdmin) and
   --#      Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp and
   --#
   --#      --------------------------------------------------------
   --#      -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
   --#      --====================================================--
   --#      -- Before each call to ShutdownOp, the security       --
   --#      -- property holds.                                    --
   --#      --------------------------------------------------------
   --#      ( ( Latch.IsLocked(Latch.State) and
   --#          Door.TheCurrentDoor(Door.State) = Door.Open and
   --#          Clock.GreaterThanOrEqual(Clock.TheCurrentTime(Clock.CurrentTime),
   --#                                   Door.prf_alarmTimeout(Door.State)) ) <->
   --#        Door.TheDoorAlarm(Door.State) = AlarmTypes.Alarming ) and
   --#
   --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
   --#           ( AdminToken.prf_isGood(AdminToken.State) and
   --#             AdminToken.prf_authCertValid(AdminToken.State) and
   --#             AdminToken.TheAuthCertRole(AdminToken.State) = PrivTypes.Guard )) and
   --#
   --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
   --#           ( ( Admin.IsDoingOp(TheAdmin) and
   --#               Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) or
   --#             not Admin.IsDoingOp(TheAdmin) ));
   --#
   --# post ( Status = Shutdown or
   --#        Status = WaitingStartAdminOp ) and
   --#
   --#      ( Status = WaitingStartAdminOp ->
   --#        ( Admin.prf_rolePresent(TheAdmin) = Admin.prf_rolePresent(TheAdmin~) and
   --#          Admin.IsPresent(TheAdmin) and
   --#          Admin.IsDoingOp(TheAdmin) and
   --#          Latch.State = Latch.State~ and
   --#          Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp ) ) and
   --#
   --#      ( Status = Shutdown ->
   --#        ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.UserOnly and
   --#          Latch.IsLocked(Latch.State) and
   --#          not Admin.IsDoingOp(TheAdmin) ) ) and
   --#
   --#      ( ( Admin.IsDoingOp(TheAdmin) and
   --#          Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp ) ->
   --#                    Status = WaitingStartAdminOp ) and
   --#
   --#      --------------------------------------------------------
   --#      -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
   --#      --====================================================--
   --#      -- After each call to ShutdownOp, the security        --
   --#      -- property holds.                                    --
   --#      --------------------------------------------------------
   --#      ( ( Latch.IsLocked(Latch.State) and
   --#          Door.TheCurrentDoor(Door.State) = Door.Open and
   --#          Clock.GreaterThanOrEqual(Clock.TheCurrentTime(Clock.CurrentTime),
   --#                                   Door.prf_alarmTimeout(Door.State)) ) <->
   --#        Door.TheDoorAlarm(Door.State) = AlarmTypes.Alarming ) and
   --#
   --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
   --#           ( AdminToken.prf_isGood(AdminToken.State) and
   --#             AdminToken.prf_authCertValid(AdminToken.State) and
   --#             AdminToken.TheAuthCertRole(AdminToken.State) = PrivTypes.Guard )) and
   --#
   --#      ( ( not Latch.IsLocked(Latch.State) and Latch.IsLocked(Latch.State~) )
   --#        ->
   --#        ( ( AdminToken.prf_isGood(AdminToken.State) and
   --#            AdminToken.prf_authCertValid(AdminToken.State) and
   --#            AdminToken.TheAuthCertRole(AdminToken.State) = PrivTypes.Guard )
   --#        )
   --#      ) and
   --#
   --#      ( ( Admin.IsDoingOp(TheAdmin) and
   --#          Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) ->
   --#           Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ) and
   --#
   --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
   --#           ( ( Admin.IsDoingOp(TheAdmin) and
   --#               Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) or
   --#             not Admin.IsDoingOp(TheAdmin) ));
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
           ( ElementID   => AuditTypes.Shutdown,
             Severity    => AuditTypes.Information,
             User        => AdminToken.ExtractUser,
             Description => AuditTypes.NoDescription
             );

         UserToken.Clear;
         AdminToken.Clear;

         --# check Admin.prf_rolePresent (TheAdmin) /= PrivTypes.Guard;

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
   --# global in     Clock.CurrentTime;
   --#        in     Clock.Now;
   --#        in     Floppy.Input;
   --#        in out AdminToken.State;
   --#        in out Status;
   --#        in out Screen.State;
   --#        in out Display.State;
   --#        in out Floppy.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#        in out ConfigData.State;
   --#        in out ConfigData.FileState;
   --#        in out Door.State;
   --#        in out Latch.State;
   --#        in out UserToken.State;
   --#           out Floppy.Output;
   --#        in out Floppy.WrittenState;
   --# derives AdminToken.State,
   --#         Display.State,
   --#         UserToken.State      from *,
   --#                                   TheAdmin,
   --#                                   Door.State &
   --#         Screen.State         from *,
   --#                                   Status,
   --#                                   Floppy.State,
   --#                                   Floppy.WrittenState,
   --#                                   Floppy.Input,
   --#                                   TheAdmin,
   --#                                   Door.State &
   --#         Status               from *,
   --#                                   Status,
   --#                                   Floppy.State,
   --#                                   TheAdmin,
   --#                                   Door.State &
   --#         AuditLog.State,
   --#         AuditLog.FileState   from AdminToken.State,
   --#                                   Status,
   --#                                   Clock.CurrentTime,
   --#                                   Screen.State,
   --#                                   Display.State,
   --#                                   Floppy.State,
   --#                                   Floppy.Input,
   --#                                   Floppy.WrittenState,
   --#                                   AuditLog.State,
   --#                                   AuditLog.FileState,
   --#                                   ConfigData.State,
   --#                                   Clock.Now,
   --#                                   TheAdmin,
   --#                                   ConfigData.FileState,
   --#                                   Door.State,
   --#                                   Latch.State &
   --#         ConfigData.State,
   --#         ConfigData.FileState from *,
   --#                                   Status,
   --#                                   Floppy.State,
   --#                                   TheAdmin &
   --#         Door.State,
   --#         Latch.State          from Clock.CurrentTime,
   --#                                   ConfigData.State,
   --#                                   TheAdmin,
   --#                                   Door.State,
   --#                                   Latch.State &
   --#         Floppy.State         from *,
   --#                                   Status,
   --#                                   Floppy.Input,
   --#                                   TheAdmin &
   --#         TheAdmin             from *,
   --#                                   Status,
   --#                                   Door.State &
   --#         Floppy.Output from Floppy.State, Status, TheAdmin,
   --#                                   AuditLog.State,
   --#                                   AuditLog.FileState &
   --#         Floppy.WrittenState from *, Floppy.State, Status,
   --#                                   AuditLog.State, TheAdmin,
   --#                                   AuditLog.FileState;
   --# pre  ( Status = WaitingStartAdminOp or
   --#        Status = WaitingFinishAdminOp ) and
   --#
   --#      ( ( Admin.IsDoingOp(TheAdmin) and
   --#          Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp ) ->
   --#                    Status = WaitingStartAdminOp ) and
   --#
   --#      Admin.IsPresent(TheAdmin) and
   --#      Admin.IsDoingOp(TheAdmin) and
   --#
   --#      --------------------------------------------------------
   --#      -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
   --#      --====================================================--
   --#      -- Before each call to AdminOp, the security property --
   --#      -- holds.                                             --
   --#      --------------------------------------------------------
   --#      ( ( Latch.IsLocked(Latch.State) and
   --#          Door.TheCurrentDoor(Door.State) = Door.Open and
   --#          Clock.GreaterThanOrEqual(Clock.TheCurrentTime(Clock.CurrentTime),
   --#                                   Door.prf_alarmTimeout(Door.State)) ) <->
   --#        Door.TheDoorAlarm(Door.State) = AlarmTypes.Alarming ) and
   --#
   --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
   --#           ( AdminToken.prf_isGood(AdminToken.State) and
   --#             AdminToken.prf_authCertValid(AdminToken.State) and
   --#             AdminToken.TheAuthCertRole(AdminToken.State) = PrivTypes.Guard )) and
   --#
   --#      ( ( Admin.IsDoingOp(TheAdmin) and
   --#          Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) ->
   --#           Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ) and
   --#
   --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
   --#           ( ( Admin.IsDoingOp(TheAdmin) and
   --#               Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) or
   --#             not Admin.IsDoingOp(TheAdmin) ));
   --#
   --#
   --# post ( Status = WaitingStartAdminOp or
   --#        Status = WaitingFinishAdminOp or
   --#        Status = EnclaveQuiescent or
   --#        Status = Shutdown ) and
   --#
   --#      ( ( Status = WaitingStartAdminOp or
   --#          Status = WaitingFinishAdminOp ) ->
   --#        ( Admin.IsDoingOp(TheAdmin) and
   --#          Admin.IsPresent(TheAdmin) and
   --#          Admin.prf_rolePresent(TheAdmin) = Admin.prf_rolePresent(TheAdmin~) ) ) and
   --#
   --#      ( Status = EnclaveQuiescent ->
   --#        ( not Admin.IsDoingOp(TheAdmin) and
   --#          Admin.IsPresent(TheAdmin) and
   --#          Admin.prf_rolePresent(TheAdmin) = Admin.prf_rolePresent(TheAdmin~) ) ) and
   --#
   --#      ( Status = Shutdown ->
   --#        ( not Admin.IsDoingOp(TheAdmin) and
   --#          Admin.prf_rolePresent(TheAdmin) = PrivTypes.UserOnly ) ) and
   --#
   --#      ( ( Admin.IsDoingOp(TheAdmin) and
   --#          Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp ) ->
   --#                    Status = WaitingStartAdminOp ) and
   --#
   --#      --------------------------------------------------------
   --#      -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
   --#      --====================================================--
   --#      -- After each call to AdminOp, the security property  --
   --#      -- holds.                                             --
   --#      --------------------------------------------------------
   --#      ( ( Latch.IsLocked(Latch.State) and
   --#          Door.TheCurrentDoor(Door.State) = Door.Open and
   --#          Clock.GreaterThanOrEqual(Clock.TheCurrentTime(Clock.CurrentTime),
   --#                                   Door.prf_alarmTimeout(Door.State)) ) <->
   --#        Door.TheDoorAlarm(Door.State) = AlarmTypes.Alarming ) and
   --#
   --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
   --#           ( AdminToken.prf_isGood(AdminToken.State) and
   --#             AdminToken.prf_authCertValid(AdminToken.State) and
   --#             AdminToken.TheAuthCertRole(AdminToken.State) = PrivTypes.Guard )) and
   --#
   --#      ( ( not Latch.IsLocked(Latch.State) and Latch.IsLocked(Latch.State~) )
   --#        ->
   --#        ( ( AdminToken.prf_isGood(AdminToken.State) and
   --#            AdminToken.prf_authCertValid(AdminToken.State) and
   --#            AdminToken.TheAuthCertRole(AdminToken.State) = PrivTypes.Guard )
   --#        )
   --#      ) and
   --#
   --#      ( ( Admin.IsDoingOp(TheAdmin) and
   --#          Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) ->
   --#           Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ) and
   --#
   --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
   --#           ( ( Admin.IsDoingOp(TheAdmin) and
   --#               Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) or
   --#             not Admin.IsDoingOp(TheAdmin) )) and
   --#
   --# --     ( Latch.IsLocked(Latch.State) <->
   --# --       Clock.GreaterThanOrEqual(Clock.TheCurrentTime(Clock.CurrentTime),
   --# --                                Latch.prf_LatchTimeout(Latch.State)) ) and
   --#
   --#      ( ( not Latch.IsLocked(Latch.State) and Latch.IsLocked(Latch.State~) )
   --#        -> ( Admin.IsDoingOp(TheAdmin~) and
   --#             Admin.TheCurrentOp(TheAdmin~) = Admin.OverrideLock ) );
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
   -- EnrolmentIsInProgress
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   function EnrolmentIsInProgress return Boolean
   --# global Status;
   is
   begin
      return Status in EnrolmentStates;
   end EnrolmentIsInProgress;


   ------------------------------------------------------------------
   -- Init
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure Init
   --# global in     KeyStore.State;
   --#           out Status;
   --# derives Status from KeyStore.State;
   --# post ( KeyStore.PrivateKeyPresent(KeyStore.State) <->
   --#           not EnrolmentIsInProgress(Status) ) and
   --#      ( EnrolmentIsInProgress(Status) or
   --#        Status = EnclaveQuiescent );
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
   function AdminMustLogout (TheAdmin : Admin.T) return Boolean
   --# global AdminToken.State,
   --#        Status,
   --#        Clock.CurrentTime;
   is
   begin

      return PresentAdminHasDeparted( TheAdmin => TheAdmin) or
             AdminTokenHasExpired( TheAdmin => TheAdmin);

   end AdminMustLogout;

   ------------------------------------------------------------------
   -- CurrentAdminActivityPossible
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   function CurrentAdminActivityPossible return Boolean
   --# global AdminToken.State,
   --#        Status;
   --# return R => (R -> Status in NonQuiescentStates);
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
      function AdminActivityInProgress return Boolean
        --# global Status;
      is
      begin
         return Status in ActiveEnclaveStates ;
      end AdminActivityInProgress;


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
   function HasShutdown return Boolean
   --# global Status;
   is
   begin
      return Status = Shutdown;
   end HasShutdown;

   ------------------------------------------------------------------
   -- EnrolOp
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure EnrolOp
   --# global in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in     Floppy.Input;
   --#        in out Status;
   --#        in out Screen.State;
   --#        in out Display.State;
   --#        in out Floppy.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#        in out KeyStore.Store;
   --#        in out KeyStore.State;
   --# derives Status,
   --#         Screen.State,
   --#         Display.State,
   --#         KeyStore.Store,
   --#         KeyStore.State     from *,
   --#                                 Status,
   --#                                 Floppy.State,
   --#                                 KeyStore.Store &
   --#         AuditLog.State,
   --#         AuditLog.FileState from Status,
   --#                                 Screen.State,
   --#                                 Display.State,
   --#                                 Floppy.State,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 ConfigData.State,
   --#                                 Clock.Now,
   --#                                 KeyStore.Store &
   --#         Floppy.State       from *,
   --#                                 Status,
   --#                                 Floppy.Input;
   --# pre EnrolmentIsInProgress(Status) and
   --#     not KeyStore.PrivateKeyPresent(KeyStore.State);
   --# post ( KeyStore.PrivateKeyPresent(KeyStore.State) <->
   --#           not EnrolmentIsInProgress(Status) ) and
   --#      ( EnrolmentIsInProgress(Status) or
   --#        Status = EnclaveQuiescent );
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

      --# check EnrolmentIsInProgress(Status) <-> Status in EnrolmentStates;

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
   --# global in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in out AdminToken.State;
   --#        in out Status;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --# derives AdminToken.State,
   --#         Status             from *,
   --#                                 AdminToken.State,
   --#                                 Status,
   --#                                 TheAdmin &
   --#         AuditLog.State,
   --#         AuditLog.FileState from AdminToken.State,
   --#                                 Status,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 ConfigData.State,
   --#                                 Clock.Now,
   --#                                 TheAdmin &
   --#         TheAdmin           from ;
   --# pre not EnrolmentIsInProgress(Status) and
   --#      ( ( Status = WaitingStartAdminOp or
   --#          Status = WaitingFinishAdminOp ) ->
   --#        ( Admin.IsDoingOp(TheAdmin) and
   --#          Admin.IsPresent(TheAdmin) ) );
   --# post not EnrolmentIsInProgress(Status) and
   --#      Admin.prf_rolePresent(TheAdmin) = PrivTypes.UserOnly and
   --#      not Admin.IsDoingOp(TheAdmin) and
   --#      ( Status = EnclaveQuiescent or
   --#        Status = WaitingRemoveAdminTokenFail or
   --#        Status = Status~ ) and
   --#      not ( Status = WaitingStartAdminOp or
   --#            Status = WaitingFinishAdminOp );
   is
   begin
      if PresentAdminHasDeparted(TheAdmin) then
         if Status = EnclaveQuiescent then

            -- TokenRemovedAdminLogoutC actions
            AuditLog.AddElementToLog
              ( ElementID   => AuditTypes.AdminTokenRemoved,
                Severity    => AuditTypes.Information,
                User        => AdminToken.ExtractUser,
                Description => AuditTypes.NoDescription
                );

            AdminTokenTear;

         elsif Status = WaitingStartAdminOp or
                Status = WaitingFinishAdminOp then

            -- BadAdminLogoutC
            BadAdminTokenTear;

         end if;
      else -- AdminTokenHasExpired

         -- AdminTokenTimeoutC actions
         AuditLog.AddElementToLog
           ( ElementID   => AuditTypes.AdminTokenExpired,
             Severity    => AuditTypes.Warning,
             User        => AdminToken.ExtractUser,
             Description => AuditTypes.NoDescription
             );

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
   --# global in     Clock.CurrentTime;
   --#        in     Clock.Now;
   --#        in     Floppy.Input;
   --#        in     KeyStore.Store;
   --#        in     KeyStore.State;
   --#        in     AdminToken.Input;
   --#        in out AdminToken.State;
   --#        in out Status;
   --#        in out Screen.State;
   --#        in out Display.State;
   --#        in out Floppy.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#        in out ConfigData.State;
   --#        in out AdminToken.Status;
   --#        in out ConfigData.FileState;
   --#        in out Door.State;
   --#        in out Latch.State;
   --#        in out UserToken.State;
   --#           out Floppy.Output;
   --#        in out Floppy.WrittenState;
   --# derives AdminToken.State,
   --#         TheAdmin             from AdminToken.State,
   --#                                   Status,
   --#                                   Clock.CurrentTime,
   --#                                   KeyStore.Store,
   --#                                   KeyStore.State,
   --#                                   TheAdmin,
   --#                                   AdminToken.Status,
   --#                                   AdminToken.Input,
   --#                                   Door.State &
   --#         Screen.State         from *,
   --#                                   AdminToken.State,
   --#                                   Status,
   --#                                   Clock.CurrentTime,
   --#                                   Floppy.State,
   --#                                   Floppy.WrittenState,
   --#                                   Floppy.Input,
   --#                                   KeyStore.Store,
   --#                                   KeyStore.State,
   --#                                   TheAdmin,
   --#                                   AdminToken.Status,
   --#                                   AdminToken.Input,
   --#                                   Door.State &
   --#         Status               from *,
   --#                                   AdminToken.State,
   --#                                   Status,
   --#                                   Clock.CurrentTime,
   --#                                   Floppy.State,
   --#                                   KeyStore.Store,
   --#                                   KeyStore.State,
   --#                                   TheAdmin,
   --#                                   AdminToken.Status,
   --#                                   AdminToken.Input,
   --#                                   Door.State &
   --#         Display.State,
   --#         UserToken.State      from *,
   --#                                   Status,
   --#                                   TheAdmin,
   --#                                   Door.State &
   --#         AuditLog.State,
   --#         AuditLog.FileState   from AdminToken.State,
   --#                                   Status,
   --#                                   Clock.CurrentTime,
   --#                                   Screen.State,
   --#                                   Display.State,
   --#                                   Floppy.State,
   --#                                   AuditLog.State,
   --#                                   Floppy.Input,
   --#                                   Floppy.WrittenState,
   --#                                   AuditLog.FileState,
   --#                                   ConfigData.State,
   --#                                   Clock.Now,
   --#                                   KeyStore.Store,
   --#                                   KeyStore.State,
   --#                                   TheAdmin,
   --#                                   AdminToken.Status,
   --#                                   AdminToken.Input,
   --#                                   ConfigData.FileState,
   --#                                   Door.State,
   --#                                   Latch.State &
   --#         ConfigData.State,
   --#         ConfigData.FileState from *,
   --#                                   Status,
   --#                                   Floppy.State,
   --#                                   TheAdmin &
   --#         Door.State,
   --#         Latch.State          from Status,
   --#                                   Clock.CurrentTime,
   --#                                   ConfigData.State,
   --#                                   TheAdmin,
   --#                                   Door.State,
   --#                                   Latch.State &
   --#         Floppy.State         from *,
   --#                                   Status,
   --#                                   Floppy.Input,
   --#                                   TheAdmin &
   --#         AdminToken.Status    from *,
   --#                                   AdminToken.State,
   --#                                   Status &
   --#         Floppy.Output from Floppy.State, Status, TheAdmin,
   --#                                   AuditLog.State,
   --#                                   AuditLog.FileState &
   --#         Floppy.WrittenState from *, Floppy.State, Status,
   --#                                   AuditLog.State, TheAdmin,
   --#                                   AuditLog.FileState;
   --#
   --# pre not EnrolmentIsInProgress(Status) and
   --#     CurrentAdminActivityPossible(AdminToken.State, Status) and
   --#      --------------------------------------------------------
   --#      -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
   --#      --====================================================--
   --#      -- Before each call to ProgressAdminActivity, the     --
   --#      -- security property holds.                           --
   --#      --------------------------------------------------------
   --#      ( ( Latch.IsLocked(Latch.State) and
   --#          Door.TheCurrentDoor(Door.State) = Door.Open and
   --#          Clock.GreaterThanOrEqual(Clock.TheCurrentTime(Clock.CurrentTime),
   --#                                   Door.prf_alarmTimeout(Door.State)) ) <->
   --#        Door.TheDoorAlarm(Door.State) = AlarmTypes.Alarming ) and
   --#
   --#      ( ( Status = GotAdminToken or
   --#          Status = WaitingRemoveAdminTokenFail ) -> not Admin.IsPresent(TheAdmin) ) and
   --#
   --#      ( not Admin.IsPresent(TheAdmin) -> not Admin.IsDoingOp(TheAdmin) ) and
   --#
   --#      ( ( Status = WaitingStartAdminOp or
   --#          Status = WaitingFinishAdminOp ) ->
   --#        ( Admin.IsPresent(TheAdmin) and
   --#          Admin.IsDoingOp(TheAdmin) ) ) and
   --#
   --#      ( Status = EnclaveQuiescent ->
   --#        not Admin.IsDoingOp(TheAdmin) ) and
   --#
   --#      ( Status = Shutdown ->
   --#        ( not Admin.IsDoingOp(TheAdmin) and
   --#          Admin.prf_rolePresent(TheAdmin) = PrivTypes.UserOnly ) ) and
   --#
   --#      ( ( Admin.IsDoingOp(TheAdmin) and
   --#          Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp ) ->
   --#                    Status = WaitingStartAdminOp ) and
   --#
   --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
   --#           ( AdminToken.prf_isGood(AdminToken.State) and
   --#             AdminToken.prf_authCertValid(AdminToken.State) and
   --#             AdminToken.TheAuthCertRole(AdminToken.State) = PrivTypes.Guard )) and
   --#
   --#      ( ( Admin.IsDoingOp(TheAdmin) and
   --#          Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) ->
   --#           Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ) and
   --#
   --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
   --#           ( ( Admin.IsDoingOp(TheAdmin) and
   --#               Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) or
   --#             not Admin.IsDoingOp(TheAdmin) ));
   --#
   --#
   --# post not EnrolmentIsInProgress(Status) and
   --#      --------------------------------------------------------
   --#      -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
   --#      --====================================================--
   --#      -- After each call to ProgressAdminActivity, the      --
   --#      -- security property holds.                           --
   --#      --------------------------------------------------------
   --#      ( ( Latch.IsLocked(Latch.State) and
   --#          Door.TheCurrentDoor(Door.State) = Door.Open and
   --#          Clock.GreaterThanOrEqual(Clock.TheCurrentTime(Clock.CurrentTime),
   --#                                   Door.prf_alarmTimeout(Door.State)) ) <->
   --#        Door.TheDoorAlarm(Door.State) = AlarmTypes.Alarming ) and
   --#
   --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
   --#           ( AdminToken.prf_isGood(AdminToken.State) and
   --#             AdminToken.prf_authCertValid(AdminToken.State) and
   --#             AdminToken.TheAuthCertRole(AdminToken.State) = PrivTypes.Guard )) and
   --#
   --#      ( ( not Latch.IsLocked(Latch.State) and Latch.IsLocked(Latch.State~) )
   --#        ->
   --#        ( ( AdminToken.prf_isGood(AdminToken.State) and
   --#            AdminToken.prf_authCertValid(AdminToken.State) and
   --#            AdminToken.TheAuthCertRole(AdminToken.State) = PrivTypes.Guard )
   --#        )
   --#      ) and
   --#
   --#      ( ( Admin.IsDoingOp(TheAdmin) and
   --#          Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) ->
   --#           Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ) and
   --#
   --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
   --#           ( ( Admin.IsDoingOp(TheAdmin) and
   --#               Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) or
   --#             not Admin.IsDoingOp(TheAdmin) )) and
   --#
   --#      ( not Admin.IsPresent(TheAdmin) -> not Admin.IsDoingOp(TheAdmin) ) and
   --#
   --#      ( ( Status = GotAdminToken or
   --#          Status = WaitingRemoveAdminTokenFail ) -> not Admin.IsPresent(TheAdmin) ) and
   --#
   --#      ( ( Status = WaitingStartAdminOp or
   --#          Status = WaitingFinishAdminOp ) ->
   --#        ( Admin.IsDoingOp(TheAdmin) and
   --#          Admin.IsPresent(TheAdmin) and
   --#          Admin.prf_rolePresent(TheAdmin) = Admin.prf_rolePresent(TheAdmin~) ) ) and
   --#
   --#      ( Status = EnclaveQuiescent ->
   --#        ( not Admin.IsDoingOp(TheAdmin) ) ) and
   --#
   --#      ( Status = Shutdown ->
   --#        ( not Admin.IsDoingOp(TheAdmin) and
   --#          Admin.prf_rolePresent(TheAdmin) = PrivTypes.UserOnly ) ) and
   --#
   --#      ( ( Admin.IsDoingOp(TheAdmin) and
   --#          Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp ) ->
   --#                    Status = WaitingStartAdminOp ) and
   --#
   --# --     ( Latch.IsLocked(Latch.State) <->
   --# --       Clock.GreaterThanOrEqual(Clock.TheCurrentTime(Clock.CurrentTime),
   --# --                                Latch.prf_LatchTimeout(Latch.State)) ) and
   --#
   --#      ( ( not Latch.IsLocked(Latch.State) and Latch.IsLocked(Latch.State~) )
   --#        -> ( Admin.IsDoingOp(TheAdmin~) and
   --#             Admin.TheCurrentOp(TheAdmin~) = Admin.OverrideLock ) );
   is
      LocalStatus : NonQuiescentStates;
   begin
      LocalStatus := NonQuiescentStates'(Status);

      case LocalStatus is
         -- TISProgressAdminLogon
         when GotAdminToken =>
            ValidateAdminToken (TheAdmin => TheAdmin);
            --# check Status > WaitingEndEnrol;
         when WaitingRemoveAdminTokenFail =>
            CompleteFailedAdminLogon;
            --# check Admin.prf_rolePresent(TheAdmin) /= PrivTypes.Guard;
         -- TISAdminOp
         when WaitingStartAdminOp | WaitingFinishAdminOp =>
            AdminOp(TheAdmin => TheAdmin);
            --# check Status > WaitingEndEnrol;
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
   --# global in     AdminToken.State;
   --#        in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in     Keyboard.Input;
   --#        in out Status;
   --#        in out Screen.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --# derives Status,
   --#         Screen.State,
   --#         TheAdmin           from *,
   --#                                 AdminToken.State,
   --#                                 Status,
   --#                                 TheAdmin,
   --#                                 Keyboard.Input &
   --#         AuditLog.State,
   --#         AuditLog.FileState from AdminToken.State,
   --#                                 Status,
   --#                                 Screen.State,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 ConfigData.State,
   --#                                 Clock.Now,
   --#                                 TheAdmin,
   --#                                 Keyboard.Input;
   --#
   --# pre not EnrolmentIsInProgress(Status) and
   --#
   --# --     ( prf_StatusIsGotAdminToken(State) -> not Admin.IsPresent(TheAdmin) ) and
   --#
   --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
   --#           ( AdminToken.prf_isGood(AdminToken.State) and
   --#             AdminToken.prf_authCertValid(AdminToken.State) and
   --#             AdminToken.TheAuthCertRole(AdminToken.State) = PrivTypes.Guard )) and
   --#
   --#      ( not Admin.IsPresent(TheAdmin) -> not Admin.IsDoingOp(TheAdmin) ) and
   --#
   --#      ( ( Status = GotAdminToken or
   --#          Status = WaitingRemoveAdminTokenFail ) -> not Admin.IsPresent(TheAdmin) ) and
   --#
   --#      ( ( Status = WaitingStartAdminOp or
   --#          Status = WaitingFinishAdminOp ) ->
   --#        ( Admin.IsPresent(TheAdmin) and
   --#          Admin.IsDoingOp(TheAdmin) ) ) and
   --#
   --#      ( Status = EnclaveQuiescent ->
   --#        not Admin.IsDoingOp(TheAdmin) ) and
   --#
   --#      ( Status = Shutdown ->
   --#        ( not Admin.IsDoingOp(TheAdmin) and
   --#          Admin.prf_rolePresent(TheAdmin) = PrivTypes.UserOnly ) ) and
   --#
   --#      ( ( Admin.IsDoingOp(TheAdmin) and
   --#          Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) ->
   --#           Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ) and
   --#
   --#      ( ( Admin.IsDoingOp(TheAdmin) and
   --#          Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp ) ->
   --#                    Status = WaitingStartAdminOp ) and
   --#
   --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
   --#           ( ( Admin.IsDoingOp(TheAdmin) and
   --#               Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) or
   --#             not Admin.IsDoingOp(TheAdmin) ));
   --#
   --#
   --# post not EnrolmentIsInProgress(Status) and
   --#
   --#      ( not Admin.IsPresent(TheAdmin) -> not Admin.IsDoingOp(TheAdmin) ) and
   --#
   --#      ( ( Status = GotAdminToken or
   --#          Status = WaitingRemoveAdminTokenFail ) -> not Admin.IsPresent(TheAdmin) ) and
   --#
   --#      ( ( Status = WaitingStartAdminOp or
   --#          Status = WaitingFinishAdminOp ) ->
   --#        ( Admin.IsDoingOp(TheAdmin) and
   --#          Admin.IsPresent(TheAdmin) and
   --#          Admin.prf_rolePresent(TheAdmin) = Admin.prf_rolePresent(TheAdmin~) ) ) and
   --#
   --#      ( Status = EnclaveQuiescent ->
   --#        ( not Admin.IsDoingOp(TheAdmin) and
   --#          Admin.prf_rolePresent(TheAdmin) = Admin.prf_rolePresent(TheAdmin~) ) ) and
   --#
   --#      ( Status = Shutdown ->
   --#        ( not Admin.IsDoingOp(TheAdmin) and
   --#          Admin.prf_rolePresent(TheAdmin) = PrivTypes.UserOnly ) ) and
   --#
   --#      ( ( Admin.IsDoingOp(TheAdmin) and
   --#          Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp ) ->
   --#                    Status = WaitingStartAdminOp ) and
   --#
   --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
   --#           ( AdminToken.prf_isGood(AdminToken.State) and
   --#             AdminToken.prf_authCertValid(AdminToken.State) and
   --#             AdminToken.TheAuthCertRole(AdminToken.State) = PrivTypes.Guard )) and
   --#
   --#      ( ( Admin.IsDoingOp(TheAdmin) and
   --#          Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) ->
   --#           Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ) and
   --#
   --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
   --#           ( ( Admin.IsDoingOp(TheAdmin) and
   --#               Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) or
   --#             not Admin.IsDoingOp(TheAdmin) ));
   --#
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
      function AdminLogonCanStart return Boolean
      --# global AdminToken.State,
      --#        Status,
      --#        TheAdmin;
      --# return R => (R -> not Admin.IsPresent(TheAdmin));
      is
      begin
         return ( not Admin.IsPresent(TheAdmin)
                  and Status = EnclaveQuiescent
                  and AdminToken.IsPresent );
      end AdminLogonCanStart;


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
      function AdminOpCanStart return Boolean
      --# global AdminToken.State,
      --#        Status,
      --#        TheAdmin;
      --# return R => ((R -> Status = EnclaveQuiescent) and
      --#              (R -> Admin.IsPresent(TheAdmin)));
      is
      begin
         return ( Admin.IsPresent(TheAdmin)
                  and Status = EnclaveQuiescent
                  and AdminToken.IsPresent );
      end AdminOpCanStart;


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
      --# global in     AdminToken.State;
      --#        in     ConfigData.State;
      --#        in     Clock.Now;
      --#        in     Keyboard.Input;
      --#        in out Status;
      --#        in out Screen.State;
      --#        in out AuditLog.State;
      --#        in out AuditLog.FileState;
      --#        in out TheAdmin;
      --# derives Status,
      --#         Screen.State,
      --#         TheAdmin           from *,
      --#                                 TheAdmin,
      --#                                 Keyboard.Input &
      --#         AuditLog.State,
      --#         AuditLog.FileState from AdminToken.State,
      --#                                 Screen.State,
      --#                                 AuditLog.State,
      --#                                 AuditLog.FileState,
      --#                                 ConfigData.State,
      --#                                 Clock.Now,
      --#                                 TheAdmin,
      --#                                 Keyboard.Input;
      --# pre AdminOpCanStart(AdminToken.State, Status, TheAdmin) and
      --#     Status = EnclaveQuiescent and
      --#
      --#     Admin.IsPresent(TheAdmin) and
      --#     not Admin.IsDoingOp(TheAdmin) and
      --#
      --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
      --#           ( AdminToken.prf_isGood(AdminToken.State) and
      --#             AdminToken.prf_authCertValid(AdminToken.State) and
      --#             AdminToken.TheAuthCertRole(AdminToken.State) = PrivTypes.Guard )) and
      --#
      --#      ( ( Admin.IsDoingOp(TheAdmin) and
      --#          Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) ->
      --#           Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ) and
      --#
      --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
      --#           ( ( Admin.IsDoingOp(TheAdmin) and
      --#               Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) or
      --#             not Admin.IsDoingOp(TheAdmin) ));
      --#
      --#
      --# post ( Status = EnclaveQuiescent or
      --#        Status = WaitingStartAdminOp ) and
      --#
      --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
      --#           ( AdminToken.prf_isGood(AdminToken.State) and
      --#             AdminToken.prf_authCertValid(AdminToken.State) and
      --#             AdminToken.TheAuthCertRole(AdminToken.State) = PrivTypes.Guard )) and
      --#
      --#      ( ( Admin.IsDoingOp(TheAdmin) and
      --#          Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) ->
      --#           Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ) and
      --#
      --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
      --#           ( ( Admin.IsDoingOp(TheAdmin) and
      --#               Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) or
      --#             not Admin.IsDoingOp(TheAdmin) )) and
      --#
      --#      ( ( Admin.IsDoingOp(TheAdmin) and
      --#          Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp ) ->
      --#                    Status = WaitingStartAdminOp ) and
      --#
      --#      ( ( Status = WaitingStartAdminOp or
      --#          Status = WaitingFinishAdminOp ) ->
      --#        ( Admin.IsDoingOp(TheAdmin) and
      --#          Admin.IsPresent(TheAdmin) and
      --#          Admin.prf_rolePresent(TheAdmin) = Admin.prf_rolePresent(TheAdmin~) ) ) and
      --#
      --#      ( Status = EnclaveQuiescent ->
      --#        ( not Admin.IsDoingOp(TheAdmin) and
      --#          Admin.prf_rolePresent(TheAdmin) = Admin.prf_rolePresent(TheAdmin~) ) ) and
      --#
      --#      ( Status = Shutdown ->
      --#        ( not Admin.IsDoingOp(TheAdmin) and
      --#          Admin.prf_rolePresent(TheAdmin) = PrivTypes.UserOnly ) );
      is
         KeyedDataPresence : BasicTypes.PresenceT;
         KeyedData         : Keyboard.DataT;
         TheOp             : Admin.OpAndNullT;
      begin
         Keyboard.Read(DataPresence => KeyedDataPresence,
                       Data         => KeyedData);

         if KeyedDataPresence = BasicTypes.Present then
            TheOp := Admin.OpIsAvailable(TheAdmin => TheAdmin,
                                         KeyedOp  => KeyedData);
            --# check TheOp /= Admin.NullOp ->
            --#         (TheOp = Admin.OverrideLock <->
            --#            Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard);

            if TheOp /= Admin.NullOp then

               -- ValidateOpRequestOK actions
               Status := WaitingStartAdminOp;

               Screen.SetMessage(Msg => Screen.DoingOp);
               Admin.StartOp(TheAdmin => TheAdmin,
                             Op       => TheOp);

               AuditLog.AddElementToLog
                 ( ElementID   => AuditTypes.OperationStart,
                   Severity    => AuditTypes.Information,
                   User        => AdminToken.ExtractUser,
                   Description => KeyedData.Text
                   );
            else

               -- ValidateOpRequestFail actions
               Screen.SetMessage(Msg => Screen.InvalidRequest);

               AuditLog.AddElementToLog
                 ( ElementID   => AuditTypes.InvalidOpRequest,
                   Severity    => AuditTypes.Warning,
                   User        => AdminToken.ExtractUser,
                   Description => KeyedData.Text
                   );
            end if;
         end if; -- NoOpRequest

      end StartAdminOp;

   ------------------------------------------------------------------
   -- begin StartAdminActivity
   ------------------------------------------------------------------
   begin
      if AdminLogonCanStart then
         Status := GotAdminToken;
         --# check not Admin.IsPresent(TheAdmin);
      elsif AdminOpCanStart then
         --# check Status = EnclaveQuiescent;
         StartAdminOp;
         --# check Status > WaitingEndEnrol ;
      end if;
   end StartAdminActivity;

   ------------------------------------------------------------------
   -- ResetScreenMessage
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure ResetScreenMessage
     (TheAdmin : in Admin.T)
   --# global in     Status;
   --#        in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#        in out Screen.State;
   --# derives Screen.State       from *,
   --#                                 Status,
   --#                                 TheAdmin &
   --#         AuditLog.State,
   --#         AuditLog.FileState from Status,
   --#                                 Screen.State,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 ConfigData.State,
   --#                                 Clock.Now,
   --#                                 TheAdmin;
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
