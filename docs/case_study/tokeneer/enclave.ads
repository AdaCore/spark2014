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
with Admin;
with KeyStore; use KeyStore;
with PrivTypes; use PrivTypes;
use Admin;
with Latch; use Latch;
with Door; use Door;
with Clock; use Clock;
with AlarmTypes; use AlarmTypes;
with AdminToken; use AdminToken;

--# inherit
--#    Admin,
--#    AdminToken,
--#    AuditLog,
--#    AuditTypes,
--#    AlarmTypes,
--#    BasicTypes,
--#    Clock,
--#    ConfigData,
--#    Configuration,
--#    Door,
--#    Display,
--#    Enrolment,
--#    File,
--#    Floppy,
--#    KeyStore,
--#    Keyboard,
--#    Latch,
--#    PrivTypes,
--#    Screen,
--#    UserToken;

package Enclave
--# own State : StateType;
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
   Status : StatusT;

   --# type StateType is Abstract;
   --# function prf_statusIsGotAdminToken(State : StateType)
   --#    return Boolean;
   --# function prf_statusIsWaitingRemoveAdminTokenFail(State : StateType)
   --#    return Boolean;
   --# function prf_statusIsWaitingStartAdminOp(State : StateType)
   --#    return Boolean;
   --# function prf_statusIsWaitingFinishAdminOp(State : StateType)
   --#    return Boolean;
   --# function prf_statusIsEnclaveQuiescent(State : StateType)
   --#    return Boolean;
   --# function prf_statusIsShutdown(State : StateType)
   --#    return Boolean;
    function statusIsGotAdminToken return Boolean;
    function statusIsWaitingRemoveAdminTokenFail return Boolean;
    function statusIsWaitingStartAdminOp return Boolean;
    function statusIsWaitingFinishAdminOp return Boolean;
    function statusIsEnclaveQuiescent return Boolean;
    function statusIsShutdown return Boolean;


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
   function EnrolmentIsInProgress return Boolean;
   --# global State;


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
   procedure Init;
   --# global in     KeyStore.State;
   --#           out State;
   --# derives State from KeyStore.State;
   --# post ( KeyStore.PrivateKeyPresent(KeyStore.State) <->
   --#           not EnrolmentIsInProgress(State) ) and
   --#      ( EnrolmentIsInProgress(State) or
   --#           prf_statusIsEnclaveQuiescent(State) );
   pragma Postcondition
     (( KeyStore.PrivateKeyPresent =
      not EnrolmentIsInProgress ) and then
        ( EnrolmentIsInProgress or else
         statusIsEnclaveQuiescent ));


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
   function AdminMustLogout (TheAdmin : Admin.T) return Boolean;
   --# global State,
   --#        Clock.CurrentTime,
   --#        AdminToken.State;


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
   function CurrentAdminActivityPossible return Boolean;
   --# global State,
   --#        AdminToken.State;


   ------------------------------------------------------------------
   -- HasShutdown
   --
   -- Description:
   --    Returns true if and only if the system is in a shutdown state.
   --
   -- traceunit : C.Enclave.HasShutdown
   -- traceto :
   ------------------------------------------------------------------
   function HasShutdown return Boolean;
   --# global State;


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
   procedure EnrolOp;
   --# global in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in     Floppy.Input;
   --#        in out State;
   --#        in out KeyStore.State;
   --#        in out Screen.State;
   --#        in out Display.State;
   --#        in out KeyStore.Store;
   --#        in out Floppy.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --# derives State,
   --#         KeyStore.State,
   --#         Screen.State,
   --#         Display.State,
   --#         KeyStore.Store     from *,
   --#                                 State,
   --#                                 KeyStore.Store,
   --#                                 Floppy.State &
   --#         AuditLog.State,
   --#         AuditLog.FileState from State,
   --#                                 Screen.State,
   --#                                 Display.State,
   --#                                 KeyStore.Store,
   --#                                 Floppy.State,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 ConfigData.State,
   --#                                 Clock.Now &
   --#         Floppy.State       from *,
   --#                                 State,
   --#                                 Floppy.Input;
   --# pre EnrolmentIsInProgress(State) and
   --#     not KeyStore.PrivateKeyPresent(KeyStore.State);
   --# post ( KeyStore.PrivateKeyPresent(KeyStore.State) <->
   --#           not EnrolmentIsInProgress(State) ) and
   --#      ( EnrolmentIsInProgress(State) or
   --#           prf_statusIsEnclaveQuiescent(State) );
   pragma Precondition
     (EnrolmentIsInProgress and then
        not KeyStore.PrivateKeyPresent);
   pragma Postcondition
     (( KeyStore.PrivateKeyPresent =
      not EnrolmentIsInProgress ) and then
     ( EnrolmentIsInProgress or else
      statusIsEnclaveQuiescent ));


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
   procedure AdminLogout
     (TheAdmin : in out Admin.T);
   --# global in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in out State;
   --#        in out AdminToken.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --# derives State,
   --#         AdminToken.State   from *,
   --#                                 State,
   --#                                 AdminToken.State,
   --#                                 TheAdmin &
   --#         AuditLog.State,
   --#         AuditLog.FileState from State,
   --#                                 AdminToken.State,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 ConfigData.State,
   --#                                 Clock.Now,
   --#                                 TheAdmin &
   --#         TheAdmin           from ;
   --# pre not EnrolmentIsInProgress(State) and
   --#      ( ( prf_statusIsWaitingStartAdminOp(State) or
   --#          prf_statusIsWaitingFinishAdminOp(State) ) ->
   --#        ( Admin.IsDoingOp(TheAdmin) and
   --#          Admin.IsPresent(TheAdmin) ) );
   --# post not EnrolmentIsInProgress(State) and
   --#      Admin.prf_rolePresent(TheAdmin) = PrivTypes.UserOnly and
   --#      not Admin.IsDoingOp(TheAdmin) and
   --#      ( prf_statusIsEnclaveQuiescent(State) or
   --#        prf_statusIsWaitingRemoveAdminTokenFail(State) or
   --#        State = State~ ) and
   --#      not ( prf_statusIsWaitingStartAdminOp(State) or
   --#            prf_statusIsWaitingFinishAdminOp(State) );
   pragma Precondition
     (not EnrolmentIsInProgress and then
         ( ( statusIsWaitingStartAdminOp or else
             statusIsWaitingFinishAdminOp ) <=
           ( Admin.IsDoingOp(TheAdmin) and then
             Admin.IsPresent(TheAdmin) ) ));
   pragma Postcondition
     (not EnrolmentIsInProgress and then
         Admin.RolePresent(TheAdmin) = PrivTypes.UserOnly and then
         not Admin.IsDoingOp(TheAdmin) and then
         ( statusIsEnclaveQuiescent or else
           statusIsWaitingRemoveAdminTokenFail or else
           Status = Status'Old ) and then
         not ( statusIsWaitingStartAdminOp or else
               statusIsWaitingFinishAdminOp ));



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
   procedure ProgressAdminActivity
     (TheAdmin : in out Admin.T);
   --# global in     KeyStore.State;
   --#        in     Clock.CurrentTime;
   --#        in     KeyStore.Store;
   --#        in     Clock.Now;
   --#        in     Floppy.Input;
   --#        in     AdminToken.Input;
   --#        in out State;
   --#        in out AdminToken.State;
   --#        in out Screen.State;
   --#        in out Display.State;
   --#        in out Floppy.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#        in out ConfigData.State;
   --#        in out Door.State;
   --#        in out AdminToken.Status;
   --#        in out ConfigData.FileState;
   --#        in out Latch.State;
   --#        in out UserToken.State;
   --#        in out Floppy.WrittenState;
   --#           out Floppy.Output;
   --# derives State                from *,
   --#                                   State,
   --#                                   KeyStore.State,
   --#                                   Clock.CurrentTime,
   --#                                   AdminToken.State,
   --#                                   KeyStore.Store,
   --#                                   Floppy.State,
   --#                                   TheAdmin,
   --#                                   Door.State,
   --#                                   AdminToken.Status,
   --#                                   AdminToken.Input &
   --#         Screen.State         from *,
   --#                                   State,
   --#                                   KeyStore.State,
   --#                                   Clock.CurrentTime,
   --#                                   AdminToken.State,
   --#                                   KeyStore.Store,
   --#                                   Floppy.State,
   --#                                   Floppy.WrittenState,
   --#                                   Floppy.Input,
   --#                                   TheAdmin,
   --#                                   Door.State,
   --#                                   AdminToken.Status,
   --#                                   AdminToken.Input &
   --#         AdminToken.State,
   --#         TheAdmin             from State,
   --#                                   KeyStore.State,
   --#                                   Clock.CurrentTime,
   --#                                   AdminToken.State,
   --#                                   KeyStore.Store,
   --#                                   TheAdmin,
   --#                                   Door.State,
   --#                                   AdminToken.Status,
   --#                                   AdminToken.Input &
   --#         Display.State,
   --#         UserToken.State      from *,
   --#                                   State,
   --#                                   TheAdmin,
   --#                                   Door.State &
   --#         AuditLog.State,
   --#         AuditLog.FileState   from State,
   --#                                   KeyStore.State,
   --#                                   Clock.CurrentTime,
   --#                                   AdminToken.State,
   --#                                   Screen.State,
   --#                                   Display.State,
   --#                                   KeyStore.Store,
   --#                                   Floppy.State,
   --#                                   Floppy.Input,
   --#                                   Floppy.WrittenState,
   --#                                   AuditLog.State,
   --#                                   AuditLog.FileState,
   --#                                   ConfigData.State,
   --#                                   Clock.Now,
   --#                                   TheAdmin,
   --#                                   Door.State,
   --#                                   AdminToken.Status,
   --#                                   AdminToken.Input,
   --#                                   ConfigData.FileState,
   --#                                   Latch.State &
   --#         ConfigData.State,
   --#         ConfigData.FileState from *,
   --#                                   State,
   --#                                   Floppy.State,
   --#                                   TheAdmin &
   --#         Door.State,
   --#         Latch.State          from State,
   --#                                   Clock.CurrentTime,
   --#                                   ConfigData.State,
   --#                                   TheAdmin,
   --#                                   Door.State,
   --#                                   Latch.State &
   --#         Floppy.State         from *,
   --#                                   State,
   --#                                   Floppy.Input,
   --#                                   TheAdmin &
   --#         AdminToken.Status    from *,
   --#                                   State,
   --#                                   AdminToken.State &
   --#         Floppy.Output from Floppy.State, State, TheAdmin,
   --#                                   AuditLog.State,
   --#                                   AuditLog.FileState &
   --#         Floppy.WrittenState from *, Floppy.State, State,
   --#                                   AuditLog.State, TheAdmin,
   --#                                   AuditLog.FileState;
   --# pre not EnrolmentIsInProgress(State) and
   --#     CurrentAdminActivityPossible(State, AdminToken.State) and
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
   --#      ( ( prf_statusIsGotAdminToken(State) or
   --#          prf_statusIsWaitingRemoveAdminTokenFail(State) ) ->
   --#        not Admin.IsPresent(TheAdmin) ) and
   --#
   --#      ( not Admin.IsPresent(TheAdmin) -> not Admin.IsDoingOp(TheAdmin) ) and
   --#
   --#      ( ( prf_statusIsWaitingStartAdminOp(State) or
   --#          prf_statusIsWaitingFinishAdminOp(State) ) ->
   --#        ( Admin.IsPresent(TheAdmin) and
   --#          Admin.IsDoingOp(TheAdmin) ) ) and
   --#
   --#      ( prf_statusIsEnclaveQuiescent(State) ->
   --#        not Admin.IsDoingOp(TheAdmin) ) and
   --#
   --#      ( prf_statusIsShutdown(State) ->
   --#        ( not Admin.IsDoingOp(TheAdmin) and
   --#          Admin.prf_rolePresent(TheAdmin) = PrivTypes.UserOnly ) ) and
   --#
   --#      ( ( Admin.IsDoingOp(TheAdmin) and
   --#          Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp ) ->
   --#                    prf_statusIsWaitingStartAdminOp(State) ) and
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
   --# post not EnrolmentIsInProgress(State) and
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
   --#      ( ( prf_statusIsGotAdminToken(State) or
   --#          prf_statusIsWaitingRemoveAdminTokenFail(State) ) ->
   --#        not Admin.IsPresent(TheAdmin) ) and
   --#
   --#      ( ( prf_statusIsWaitingStartAdminOp(State) or
   --#          prf_statusIsWaitingFinishAdminOp(State) ) ->
   --#        ( Admin.IsDoingOp(TheAdmin) and
   --#          Admin.IsPresent(TheAdmin) and
   --#          Admin.prf_rolePresent(TheAdmin) = Admin.prf_rolePresent(TheAdmin~) ) ) and
   --#
   --#      ( prf_statusIsEnclaveQuiescent(State) ->
   --#        ( not Admin.IsDoingOp(TheAdmin) ) ) and
   --#
   --#      ( prf_statusIsShutdown(State) ->
   --#        ( not Admin.IsDoingOp(TheAdmin) and
   --#          Admin.prf_rolePresent(TheAdmin) = PrivTypes.UserOnly ) ) and
   --#
   --#      ( ( Admin.IsDoingOp(TheAdmin) and
   --#          Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp ) ->
   --#                    prf_statusIsWaitingStartAdminOp(State) ) and
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
   --#      ( not Admin.IsPresent(TheAdmin) -> not Admin.IsDoingOp(TheAdmin) ) and
   --#
   --#      ( ( not Latch.IsLocked(Latch.State) and Latch.IsLocked(Latch.State~) )
   --#        ->
   --#        ( ( AdminToken.prf_isGood(AdminToken.State) and
   --#            AdminToken.prf_authCertValid(AdminToken.State) and
   --#            AdminToken.TheAuthCertRole(AdminToken.State) = PrivTypes.Guard )
   --#        )
   --#      ) and
   --#
   --#      ( ( not Latch.IsLocked(Latch.State) and Latch.IsLocked(Latch.State~) )
   --#        -> ( Admin.IsDoingOp(TheAdmin~) and
   --#              Admin.TheCurrentOp(TheAdmin~) = Admin.OverrideLock ) );
   pragma Precondition
     (not EnrolmentIsInProgress and then
        CurrentAdminActivityPossible and then

         ( ( Latch.IsLocked and then
             Door.TheCurrentDoor = Door.Open and then
             Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
                                      Door.Alarm_Timeout) ) =
           (Door.TheDoorAlarm = AlarmTypes.Alarming) ) and then

         ( ( statusIsGotAdminToken or else
             statusIsWaitingRemoveAdminTokenFail ) <=
           (not Admin.IsPresent(TheAdmin)) ) and then

        ( (not Admin.IsPresent(TheAdmin)) <=
         (not Admin.IsDoingOp(TheAdmin)) ) and then

         ( ( statusIsWaitingStartAdminOp or else
             statusIsWaitingFinishAdminOp ) <=
           ( Admin.IsPresent(TheAdmin) and then
             Admin.IsDoingOp(TheAdmin) ) ) and then

         ( statusIsEnclaveQuiescent <=
           (not Admin.IsDoingOp(TheAdmin)) ) and then

         ( statusIsShutdown <=
           ( not Admin.IsDoingOp(TheAdmin) and then
             Admin.RolePresent(TheAdmin) = PrivTypes.UserOnly ) ) and then

         ( ( Admin.IsDoingOp(TheAdmin) and then
             Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp ) <=
                       statusIsWaitingStartAdminOp ) and then

         ( (Admin.RolePresent(TheAdmin) = PrivTypes.Guard) <=
              ( AdminToken.IsGood and then
                AdminToken.AuthCertValid and then
                AdminToken.TheAuthCertRole = PrivTypes.Guard )) and then

         ( ( Admin.IsDoingOp(TheAdmin) and then
             Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) <=
              (Admin.RolePresent(TheAdmin) = PrivTypes.Guard) ) and then

         ( (Admin.RolePresent(TheAdmin) = PrivTypes.Guard) <=
              ( ( Admin.IsDoingOp(TheAdmin) and then
                  Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) or else
                not Admin.IsDoingOp(TheAdmin) )));

   pragma Postcondition
     (not EnrolmentIsInProgress and then

         ( ( Latch.IsLocked and then
             Door.TheCurrentDoor = Door.Open and then
             Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
                                      Door.Alarm_Timeout) ) =
           (Door.TheDoorAlarm = AlarmTypes.Alarming) ) and then

         ( ( statusIsGotAdminToken or else
             statusIsWaitingRemoveAdminTokenFail ) <=
           (not Admin.IsPresent(TheAdmin)) ) and then

         ( ( statusIsWaitingStartAdminOp or else
             statusIsWaitingFinishAdminOp ) <=
           ( Admin.IsDoingOp(TheAdmin) and then
             Admin.IsPresent(TheAdmin) and then
            Admin.RolePresent(TheAdmin) =
              Admin.RolePresent(TheAdmin)'Old ) ) and then

         ( statusIsEnclaveQuiescent <=
           ( not Admin.IsDoingOp(TheAdmin) ) ) and then

         ( statusIsShutdown <=
           ( not Admin.IsDoingOp(TheAdmin) and then
             Admin.RolePresent(TheAdmin) = PrivTypes.UserOnly ) ) and then

         ( ( Admin.IsDoingOp(TheAdmin) and then
             Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp ) <=
                       statusIsWaitingStartAdminOp ) and then

         ( (Admin.RolePresent(TheAdmin) = PrivTypes.Guard) <=
              ( AdminToken.IsGood and then
                AdminToken.AuthCertValid and then
                AdminToken.TheAuthCertRole = PrivTypes.Guard )) and then

         ( ( Admin.IsDoingOp(TheAdmin) and then
             Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) <=
              (Admin.RolePresent(TheAdmin) = PrivTypes.Guard) ) and then

         ( (Admin.RolePresent(TheAdmin) = PrivTypes.Guard) <=
              ( ( Admin.IsDoingOp(TheAdmin) and then
                  Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) or else
                not Admin.IsDoingOp(TheAdmin) )) and then

        ( (not Admin.IsPresent(TheAdmin)) <=
         (not Admin.IsDoingOp(TheAdmin)) ) and then

        ( ( not Latch.IsLocked and then
         Latch.IsLocked'Old )
           <=
           ( ( AdminToken.IsGood and then
               AdminToken.AuthCertValid and then
               AdminToken.TheAuthCertRole = PrivTypes.Guard )
           )
         ) and then

         ( ( not Latch.IsLocked and then Latch.IsLocked'Old )
           <= ( Admin.IsDoingOp(TheAdmin)'Old and then
                 Admin.TheCurrentOp(TheAdmin)'Old = Admin.OverrideLock ) ));

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
   procedure StartAdminActivity
     (TheAdmin : in out Admin.T);
   --# global in     AdminToken.State;
   --#        in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in     Keyboard.Input;
   --#        in out State;
   --#        in out Screen.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --# derives State,
   --#         Screen.State,
   --#         TheAdmin           from *,
   --#                                 State,
   --#                                 AdminToken.State,
   --#                                 TheAdmin,
   --#                                 Keyboard.Input &
   --#         AuditLog.State,
   --#         AuditLog.FileState from State,
   --#                                 AdminToken.State,
   --#                                 Screen.State,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 ConfigData.State,
   --#                                 Clock.Now,
   --#                                 TheAdmin,
   --#                                 Keyboard.Input;
   --#
   --# pre not EnrolmentIsInProgress(State) and
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
   --#      ( not Admin.IsPresent(TheAdmin) -> not Admin.IsDoingOp(TheAdmin) ) and
   --#
   --#      ( ( prf_statusIsGotAdminToken(State) or
   --#          prf_statusIsWaitingRemoveAdminTokenFail(State) ) ->
   --#        not Admin.IsPresent(TheAdmin) ) and
   --#
   --#      ( ( prf_statusIsWaitingStartAdminOp(State) or
   --#          prf_statusIsWaitingFinishAdminOp(State) ) ->
   --#        ( Admin.IsPresent(TheAdmin) and
   --#          Admin.IsDoingOp(TheAdmin) ) ) and
   --#
   --#      ( prf_statusIsEnclaveQuiescent(State) ->
   --#        not Admin.IsDoingOp(TheAdmin) ) and
   --#
   --#      ( prf_statusIsShutdown(State) ->
   --#        ( not Admin.IsDoingOp(TheAdmin) and
   --#          Admin.prf_rolePresent(TheAdmin) = PrivTypes.UserOnly ) ) and
   --#
   --#      ( ( Admin.IsDoingOp(TheAdmin) and
   --#          Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp ) ->
   --#                    prf_statusIsWaitingStartAdminOp(State) ) and
   --#
   --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
   --#           ( ( Admin.IsDoingOp(TheAdmin) and
   --#               Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock ) or
   --#             not Admin.IsDoingOp(TheAdmin) ));
   --#
   --# post not EnrolmentIsInProgress(State) and
   --#
   --#      ( not Admin.IsPresent(TheAdmin) -> not Admin.IsDoingOp(TheAdmin) ) and
   --#
   --#      ( ( prf_statusIsGotAdminToken(State) or
   --#          prf_statusIsWaitingRemoveAdminTokenFail(State) ) ->
   --#        not Admin.IsPresent(TheAdmin) ) and
   --#
   --#      ( ( prf_statusIsWaitingStartAdminOp(State) or
   --#          prf_statusIsWaitingFinishAdminOp(State) ) ->
   --#        ( Admin.IsDoingOp(TheAdmin) and
   --#          Admin.IsPresent(TheAdmin) and
   --#          Admin.prf_rolePresent(TheAdmin) = Admin.prf_rolePresent(TheAdmin~) ) ) and
   --#
   --#      ( prf_statusIsEnclaveQuiescent(State) ->
   --#        ( not Admin.IsDoingOp(TheAdmin) and
   --#          Admin.prf_rolePresent(TheAdmin) = Admin.prf_rolePresent(TheAdmin~) ) ) and
   --#
   --#      ( prf_statusIsShutdown(State) ->
   --#        ( not Admin.IsDoingOp(TheAdmin) and
   --#          Admin.prf_rolePresent(TheAdmin) = PrivTypes.UserOnly ) ) and
   --#
   --#      ( ( Admin.IsDoingOp(TheAdmin) and
   --#          Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp ) ->
   --#                    prf_statusIsWaitingStartAdminOp(State) ) and
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
   procedure ResetScreenMessage
     (TheAdmin : in Admin.T);
   --# global in     State;
   --#        in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#        in out Screen.State;
   --# derives Screen.State       from *,
   --#                                 State,
   --#                                 TheAdmin &
   --#         AuditLog.State,
   --#         AuditLog.FileState from State,
   --#                                 Screen.State,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 ConfigData.State,
   --#                                 Clock.Now,
   --#                                 TheAdmin;


end Enclave;
