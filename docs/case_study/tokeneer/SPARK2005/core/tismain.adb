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
-- TIS main program
--
-- Description:
--    The TIS main program
--
-- Implementation Notes:
--    None.
------------------------------------------------------------------
with Admin;
with AdminToken;
with AuditLog;
with AuditTypes;
with CertificateStore;
with Configuration;
with Door;
with Display;
with Enclave;
with Floppy;
with Keyboard;
with KeyStore;
with Latch;
with Poll;
with Screen;
with Stats;
with Updates;
with UserToken;
with UserEntry;

--# inherit
--#    Admin,
--#    AdminToken,
--#    Alarm,
--#    AlarmTypes,
--#    AuditLog,
--#    AuditTypes,
--#    Bio,
--#    CertificateStore,
--#    Clock,
--#    Configuration,
--#    ConfigData,
--#    Door,
--#    Display,
--#    Enclave,
--#    Floppy,
--#    Keyboard,
--#    KeyStore,
--#    Latch,
--#    Poll,
--#    PrivTypes,
--#    Screen,
--#    Stats,
--#    UserEntry,
--#    UserToken,
--#    Updates;
--# main_program;
procedure TISMain
   --# global in     Keyboard.Input;
   --#        in     Floppy.Input;
   --#        in     Door.Input;
   --#        in     Clock.Now;
   --#        in     AdminToken.Input;
   --#        in     Bio.Input;
   --#        in     UserToken.Input;
   --#        in out AuditLog.FileState;
   --#        in out UserToken.Status;
   --#        in out CertificateStore.FileState;
   --#        in out UserEntry.State;
   --#        in out ConfigData.FileState;
   --#        in out AdminToken.Status;
   --#        in out KeyStore.Store;
   --#           out Door.State;
   --#           out Latch.State;
   --#           out Latch.Output;
   --#           out Alarm.Output;
   --#           out Enclave.State;
   --#           out ConfigData.State;
   --#           out AuditLog.State;
   --#           out Display.Output;
   --#           out Display.State;
   --#           out UserToken.State;
   --#           out CertificateStore.State;
   --#           out Clock.CurrentTime;
   --#           out AdminToken.State;
   --#           out KeyStore.State;
   --#           out UserToken.Output;
   --#           out Screen.State;
   --#           out Floppy.Output;
   --#           out Floppy.WrittenState;
   --#           out Floppy.State;
   --#           out Screen.Output;
   --# derives Door.State,
   --#         AuditLog.FileState,
   --#         UserToken.Status,
   --#         CertificateStore.FileState,
   --#         UserEntry.State,
   --#         Latch.State,
   --#         Latch.Output,
   --#         Alarm.Output,
   --#         Enclave.State,
   --#         ConfigData.State,
   --#         AuditLog.State,
   --#         Display.Output,
   --#         Display.State,
   --#         UserToken.State,
   --#         CertificateStore.State,
   --#         Clock.CurrentTime,
   --#         AdminToken.State,
   --#         ConfigData.FileState,
   --#         AdminToken.Status,
   --#         KeyStore.Store,
   --#         KeyStore.State,
   --#         UserToken.Output,
   --#         Screen.State,
   --#         Floppy.Output,
   --#         Floppy.WrittenState,
   --#         Floppy.State,
   --#         Screen.Output              from AuditLog.FileState,
   --#                                         UserToken.Status,
   --#                                         CertificateStore.FileState,
   --#                                         UserEntry.State,
   --#                                         ConfigData.FileState,
   --#                                         AdminToken.Status,
   --#                                         KeyStore.Store,
   --#                                         Keyboard.Input,
   --#                                         Floppy.Input,
   --#                                         Door.Input,
   --#                                         Clock.Now,
   --#                                         AdminToken.Input,
   --#                                         Bio.Input,
   --#                                         UserToken.Input;

is

   SystemFault       : Boolean;
   ShutdownCompleted : Boolean;

   TheStats : Stats.T;

   TheAdmin : Admin.T;

  --# function prf_preLatchState return Latch.StateType;
  --# function prf_preLatchOutput return Latch.OutType;

   ------------------------------------------------------------------
   -- Init
   --
   -- Description:
   --    Performs the Initialisation Activities.
   --
   -- Traceunit: C.TIS.Init
   -- Traceto: FD.TIS.TISInitIDStation
   -- Traceto: FD.TIS.TISStartup
   ------------------------------------------------------------------
   procedure Init
     --# global in     KeyStore.Store;
     --#        in     Keyboard.Input;
     --#        in     Clock.Now;
     --#        in out AuditLog.FileState;
     --#        in out UserToken.Status;
     --#        in out CertificateStore.FileState;
     --#        in out ConfigData.FileState;
     --#        in out AdminToken.Status;
     --#           out Door.State;
     --#           out Latch.State;
     --#           out Enclave.State;
     --#           out ConfigData.State;
     --#           out AuditLog.State;
     --#           out Display.State;
     --#           out UserToken.State;
     --#           out CertificateStore.State;
     --#           out AdminToken.State;
     --#           out KeyStore.State;
     --#           out Screen.State;
     --#           out Floppy.WrittenState;
     --#           out Floppy.State;
     --#           out Screen.Output;
     --#           out TheAdmin;
     --#           out TheStats;
     --# derives Door.State,
     --#         Latch.State,
     --#         Floppy.WrittenState,
     --#         Floppy.State,
     --#         TheAdmin,
     --#         TheStats                   from  &
     --#         AuditLog.FileState,
     --#         AuditLog.State             from AuditLog.FileState,
     --#                                         UserToken.Status,
     --#                                         CertificateStore.FileState,
     --#                                         ConfigData.FileState,
     --#                                         KeyStore.Store,
     --#                                         Clock.Now &
     --#         UserToken.Status,
     --#         CertificateStore.FileState,
     --#         ConfigData.FileState,
     --#         AdminToken.Status          from * &
     --#         Enclave.State,
     --#         Display.State,
     --#         KeyStore.State,
     --#         Screen.State,
     --#         Screen.Output              from KeyStore.Store &
     --#         ConfigData.State           from ConfigData.FileState &
     --#         UserToken.State            from UserToken.Status &
     --#         CertificateStore.State     from CertificateStore.FileState &
     --#         AdminToken.State           from AdminToken.Status &
     --#         null                       from Keyboard.Input;
     --# post ( not Enclave.EnrolmentIsInProgress(Enclave.State) <->
     --#             KeyStore.PrivateKeyPresent(KeyStore.State) ) and
     --#
     --#      ( Enclave.EnrolmentIsInProgress(Enclave.State) or
     --#           Enclave.prf_statusIsEnclaveQuiescent(Enclave.State) ) and
     --#
     --#      not Admin.IsPresent(TheAdmin) and
     --#      not Admin.IsDoingOp(TheAdmin) and
     --#
     --#      Admin.prf_rolePresent(TheAdmin) /= PrivTypes.Guard and
     --#
     --#      not Enclave.prf_statusIsWaitingStartAdminOp(Enclave.State) and
     --#      not Enclave.prf_statusIsWaitingFinishAdminOp(Enclave.State) and
     --#      not Enclave.prf_statusIsShutdown(Enclave.State) and
     --#
     --#      not AdminToken.prf_isGood(AdminToken.State) and
     --#      not AdminToken.prf_authCertValid(AdminToken.State) and
     --#      AdminToken.TheAuthCertRole(AdminToken.State) /= PrivTypes.Guard;
   is
   begin
      Stats.Init(TheStats);
      Admin.Init(TheAdmin);
      Floppy.Init;
      Configuration.Init;
      AuditLog.Init;
      KeyStore.Init;
      Display.Init(IsEnrolled => KeyStore.PrivateKeyPresent);
      Screen.Init(IsEnrolled => KeyStore.PrivateKeyPresent);
      Keyboard.Init;
      Latch.Init;
      Door.Init;
      CertificateStore.Init;
      UserToken.Init;
      AdminToken.Init;
      Enclave.Init;

      if KeyStore.PrivateKeyPresent then
         AuditLog.AddElementToLog
           ( ElementID   => AuditTypes.StartEnrolledTIS,
             Severity    => AuditTypes.Information,
             User        => AuditTypes.NoUser,
             Description => AuditTypes.NoDescription
             );

      else
         AuditLog.AddElementToLog
           ( ElementID   => AuditTypes.StartUnenrolledTIS,
             Severity    => AuditTypes.Information,
             User        => AuditTypes.NoUser,
             Description => AuditTypes.NoDescription
             );

      end if;
      --# check Admin.prf_rolePresent(TheAdmin) = PrivTypes.UserOnly;
   end Init;

   ------------------------------------------------------------------
   -- Processing
   --
   -- Description:
   --    Performs the TIS processing activity.
   --
   -- Traceunit: C.TIS.Processing
   -- Traceto: FD.TIS.TISMainLoop
   ------------------------------------------------------------------
   procedure Processing
     --# global in     Clock.CurrentTime;
     --#        in     Keyboard.Input;
     --#        in     Floppy.Input;
     --#        in     Clock.Now;
     --#        in     AdminToken.Input;
     --#        in     Bio.Input;
     --#        in     UserToken.Input;
     --#        in out Door.State;
     --#        in out AuditLog.FileState;
     --#        in out UserToken.Status;
     --#        in out CertificateStore.FileState;
     --#        in out UserEntry.State;
     --#        in out Latch.State;
     --#        in out Enclave.State;
     --#        in out ConfigData.State;
     --#        in out AuditLog.State;
     --#        in out Display.State;
     --#        in out UserToken.State;
     --#        in out CertificateStore.State;
     --#        in out AdminToken.State;
     --#        in out ConfigData.FileState;
     --#        in out AdminToken.Status;
     --#        in out KeyStore.Store;
     --#        in out KeyStore.State;
     --#        in out Screen.State;
     --#        in out Floppy.WrittenState;
     --#        in out Floppy.State;
     --#        in out TheAdmin;
     --#        in out TheStats;
     --#           out UserToken.Output;
     --#           out Floppy.Output;
     --# derives Door.State,
     --#         Latch.State                from Door.State,
     --#                                         UserEntry.State,
     --#                                         Latch.State,
     --#                                         Enclave.State,
     --#                                         ConfigData.State,
     --#                                         UserToken.State,
     --#                                         Clock.CurrentTime,
     --#                                         AdminToken.State,
     --#                                         TheAdmin &
     --#         AuditLog.FileState,
     --#         AuditLog.State             from Door.State,
     --#                                         AuditLog.FileState,
     --#                                         UserToken.Status,
     --#                                         CertificateStore.FileState,
     --#                                         UserEntry.State,
     --#                                         Latch.State,
     --#                                         Enclave.State,
     --#                                         ConfigData.State,
     --#                                         AuditLog.State,
     --#                                         Display.State,
     --#                                         UserToken.State,
     --#                                         CertificateStore.State,
     --#                                         Clock.CurrentTime,
     --#                                         AdminToken.State,
     --#                                         ConfigData.FileState,
     --#                                         AdminToken.Status,
     --#                                         KeyStore.Store,
     --#                                         KeyStore.State,
     --#                                         Screen.State,
     --#                                         Floppy.WrittenState,
     --#                                         Floppy.State,
     --#                                         Keyboard.Input,
     --#                                         Floppy.Input,
     --#                                         Clock.Now,
     --#                                         AdminToken.Input,
     --#                                         Bio.Input,
     --#                                         UserToken.Input,
     --#                                         TheAdmin &
     --#         CertificateStore.FileState,
     --#         CertificateStore.State     from *,
     --#                                         UserToken.Status,
     --#                                         UserEntry.State,
     --#                                         Enclave.State,
     --#                                         ConfigData.State,
     --#                                         UserToken.State,
     --#                                         CertificateStore.State,
     --#                                         Clock.CurrentTime,
     --#                                         AdminToken.State,
     --#                                         KeyStore.Store,
     --#                                         KeyStore.State,
     --#                                         TheAdmin &
     --#         Enclave.State              from *,
     --#                                         Door.State,
     --#                                         UserEntry.State,
     --#                                         Enclave.State,
     --#                                         UserToken.State,
     --#                                         Clock.CurrentTime,
     --#                                         AdminToken.State,
     --#                                         AdminToken.Status,
     --#                                         KeyStore.Store,
     --#                                         KeyStore.State,
     --#                                         Floppy.State,
     --#                                         Keyboard.Input,
     --#                                         AdminToken.Input,
     --#                                         TheAdmin &
     --#         Screen.State               from *,
     --#                                         Door.State,
     --#                                         UserEntry.State,
     --#                                         Enclave.State,
     --#                                         UserToken.State,
     --#                                         Clock.CurrentTime,
     --#                                         ConfigData.State,
     --#                                         AdminToken.State,
     --#                                         AdminToken.Status,
     --#                                         UserToken.Status,
     --#                                         KeyStore.Store,
     --#                                         KeyStore.State,
     --#                                         Floppy.State,
     --#                                         Floppy.WrittenState,
     --#                                         Bio.Input,
     --#                                         Floppy.Input,
     --#                                         Keyboard.Input,
     --#                                         AdminToken.Input,
     --#                                         UserToken.Input,
     --#                                         TheAdmin &
     --#         ConfigData.State,
     --#         ConfigData.FileState       from *,
     --#                                         UserEntry.State,
     --#                                         Enclave.State,
     --#                                         UserToken.State,
     --#                                         Clock.CurrentTime,
     --#                                         AdminToken.State,
     --#                                         Floppy.State,
     --#                                         TheAdmin &
     --#         KeyStore.Store,
     --#         KeyStore.State             from *,
     --#                                         Enclave.State,
     --#                                         KeyStore.Store,
     --#                                         Floppy.State &
     --#         UserToken.Status           from *,
     --#                                         UserEntry.State,
     --#                                         Enclave.State,
     --#                                         ConfigData.State,
     --#                                         UserToken.State,
     --#                                         CertificateStore.State,
     --#                                         Clock.CurrentTime,
     --#                                         AdminToken.State,
     --#                                         KeyStore.Store,
     --#                                         KeyStore.State,
     --#                                         UserToken.Input,
     --#                                         TheAdmin &
     --#         UserEntry.State            from *,
     --#                                         UserToken.Status,
     --#                                         Enclave.State,
     --#                                         ConfigData.State,
     --#                                         UserToken.State,
     --#                                         Clock.CurrentTime,
     --#                                         AdminToken.State,
     --#                                         KeyStore.Store,
     --#                                         KeyStore.State,
     --#                                         Bio.Input,
     --#                                         UserToken.Input,
     --#                                         TheAdmin &
     --#         Display.State              from *,
     --#                                         Door.State,
     --#                                         UserToken.Status,
     --#                                         UserEntry.State,
     --#                                         Enclave.State,
     --#                                         ConfigData.State,
     --#                                         UserToken.State,
     --#                                         CertificateStore.State,
     --#                                         Clock.CurrentTime,
     --#                                         AdminToken.State,
     --#                                         KeyStore.Store,
     --#                                         KeyStore.State,
     --#                                         Floppy.State,
     --#                                         Bio.Input,
     --#                                         UserToken.Input,
     --#                                         TheAdmin &
     --#         UserToken.State            from *,
     --#                                         Door.State,
     --#                                         UserToken.Status,
     --#                                         UserEntry.State,
     --#                                         Enclave.State,
     --#                                         ConfigData.State,
     --#                                         CertificateStore.State,
     --#                                         Clock.CurrentTime,
     --#                                         AdminToken.State,
     --#                                         KeyStore.Store,
     --#                                         KeyStore.State,
     --#                                         UserToken.Input,
     --#                                         TheAdmin &
     --#         AdminToken.State           from *,
     --#                                         Door.State,
     --#                                         UserEntry.State,
     --#                                         Enclave.State,
     --#                                         UserToken.State,
     --#                                         Clock.CurrentTime,
     --#                                         AdminToken.Status,
     --#                                         KeyStore.Store,
     --#                                         KeyStore.State,
     --#                                         AdminToken.Input,
     --#                                         TheAdmin &
     --#         AdminToken.Status          from *,
     --#                                         UserEntry.State,
     --#                                         Enclave.State,
     --#                                         UserToken.State,
     --#                                         Clock.CurrentTime,
     --#                                         AdminToken.State,
     --#                                         TheAdmin &
     --#         UserToken.Output           from UserToken.Status,
     --#                                         UserEntry.State,
     --#                                         Enclave.State,
     --#                                         ConfigData.State,
     --#                                         UserToken.State,
     --#                                         CertificateStore.State,
     --#                                         Clock.CurrentTime,
     --#                                         AdminToken.State,
     --#                                         KeyStore.Store,
     --#                                         KeyStore.State,
     --#                                         TheAdmin &
     --#         Floppy.Output              from AuditLog.FileState,
     --#                                         UserEntry.State,
     --#                                         Enclave.State,
     --#                                         AuditLog.State,
     --#                                         UserToken.State,
     --#                                         Clock.CurrentTime,
     --#                                         AdminToken.State,
     --#                                         Floppy.State,
     --#                                         TheAdmin &
     --#         Floppy.WrittenState        from *,
     --#                                         AuditLog.FileState,
     --#                                         UserEntry.State,
     --#                                         Enclave.State,
     --#                                         AuditLog.State,
     --#                                         UserToken.State,
     --#                                         Clock.CurrentTime,
     --#                                         AdminToken.State,
     --#                                         Floppy.State,
     --#                                         TheAdmin &
     --#         Floppy.State               from *,
     --#                                         UserEntry.State,
     --#                                         Enclave.State,
     --#                                         UserToken.State,
     --#                                         Clock.CurrentTime,
     --#                                         AdminToken.State,
     --#                                         Floppy.Input,
     --#                                         TheAdmin &
     --#         TheAdmin                   from *,
     --#                                         Door.State,
     --#                                         UserEntry.State,
     --#                                         Enclave.State,
     --#                                         UserToken.State,
     --#                                         Clock.CurrentTime,
     --#                                         AdminToken.State,
     --#                                         AdminToken.Status,
     --#                                         KeyStore.Store,
     --#                                         KeyStore.State,
     --#                                         Keyboard.Input,
     --#                                         AdminToken.Input &
     --#         TheStats                   from *,
     --#                                         UserEntry.State,
     --#                                         Enclave.State,
     --#                                         ConfigData.State,
     --#                                         UserToken.State,
     --#                                         Clock.CurrentTime,
     --#                                         AdminToken.State,
     --#                                         Bio.Input,
     --#                                         TheAdmin;
     --# pre  (not Enclave.EnrolmentIsInProgress(Enclave.State) <->
     --#             KeyStore.PrivateKeyPresent(KeyStore.State)) and
     --#      --------------------------------------------------------
     --#      -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
     --#      --====================================================--
     --#      -- Before each call to Processing, the security       --
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
     --#      ( ( Admin.IsDoingOp(TheAdmin) and
     --#          Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp ) ->
     --#                    Enclave.prf_statusIsWaitingStartAdminOp(Enclave.State) ) and
     --#
     --#      ( ( Enclave.prf_statusIsGotAdminToken(Enclave.State) or
     --#          Enclave.prf_statusIsWaitingRemoveAdminTokenFail(Enclave.State) ) ->
     --#        not Admin.IsPresent(TheAdmin) ) and
     --#
     --#      ( ( Enclave.prf_statusIsWaitingStartAdminOp(Enclave.State) or
     --#          Enclave.prf_statusIsWaitingFinishAdminOp(Enclave.State) ) ->
     --#        ( Admin.IsPresent(TheAdmin) and
     --#          Admin.IsDoingOp(TheAdmin) ) ) and
     --#
     --#      ( Enclave.prf_statusIsEnclaveQuiescent(Enclave.State) ->
     --#        not Admin.IsDoingOp(TheAdmin) ) and
     --#
     --#      ( Enclave.prf_statusIsShutdown(Enclave.State) ->
     --#        ( not Admin.IsDoingOp(TheAdmin) and
     --#          Admin.prf_rolePresent(TheAdmin) = PrivTypes.UserOnly ) ) and
     --#
     --#      ( Enclave.EnrolmentIsInProgress(Enclave.State) ->
     --#        ( not Admin.IsPresent(TheAdmin) and
     --#          not Admin.IsDoingOp(TheAdmin) ) );
     --#
     --#
     --# post (not Enclave.EnrolmentIsInProgress(Enclave.State) <->
     --#             KeyStore.PrivateKeyPresent(KeyStore.State)) and
     --#
     --#      --------------------------------------------------------
     --#      -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
     --#      --====================================================--
     --#      -- After each call to Processing, the security        --
     --#      -- property holds.                                    --
     --#      --------------------------------------------------------
     --#      ( ( Latch.IsLocked(Latch.State) and
     --#          Door.TheCurrentDoor(Door.State) = Door.Open and
     --#          Clock.GreaterThanOrEqual(Clock.TheCurrentTime(Clock.CurrentTime),
     --#                                   Door.prf_alarmTimeout(Door.State)) ) <->
     --#        Door.TheDoorAlarm(Door.State) = AlarmTypes.Alarming ) and
     --#
     --#      ( ( not Latch.IsLocked(Latch.State) and Latch.IsLocked(Latch.State~) )
     --#        ->
     --#        ( UserEntry.prf_UserEntryUnlockDoor or
     --#          ( AdminToken.prf_isGood(AdminToken.State) and
     --#            AdminToken.prf_authCertValid(AdminToken.State) and
     --#            AdminToken.TheAuthCertRole(AdminToken.State) = PrivTypes.Guard )
     --#        )
     --#      ) and
     --#
     --# --     ( ( not Latch.IsLocked(Latch.State) and Latch.IsLocked(Latch.State~) )
     --# --       -> ( Admin.IsDoingOp(TheAdmin~) and
     --# --             Admin.TheCurrentOp(TheAdmin~) = Admin.OverrideLock ) ) and
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
     --#      ( ( Admin.IsDoingOp(TheAdmin) and
     --#          Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp ) ->
     --#                    Enclave.prf_statusIsWaitingStartAdminOp(Enclave.State) ) and
     --#
     --#      ( ( Enclave.prf_statusIsGotAdminToken(Enclave.State) or
     --#          Enclave.prf_statusIsWaitingRemoveAdminTokenFail(Enclave.State) ) ->
     --#        not Admin.IsPresent(TheAdmin) ) and
     --#
     --#      ( ( Enclave.prf_statusIsWaitingStartAdminOp(Enclave.State) or
     --#          Enclave.prf_statusIsWaitingFinishAdminOp(Enclave.State) ) ->
     --#        ( Admin.IsDoingOp(TheAdmin) and
     --#          Admin.IsPresent(TheAdmin) and
     --#          Admin.prf_rolePresent(TheAdmin) = Admin.prf_rolePresent(TheAdmin~) ) ) and
     --#
     --#      ( Enclave.prf_statusIsEnclaveQuiescent(Enclave.State) ->
     --#        ( not Admin.IsDoingOp(TheAdmin) ) ) and
     --#
     --#      ( Enclave.prf_statusIsShutdown(Enclave.State) ->
     --#        ( not Admin.IsDoingOp(TheAdmin) and
     --#          Admin.prf_rolePresent(TheAdmin) = PrivTypes.UserOnly ) ) and
     --#
     --#      ( Enclave.EnrolmentIsInProgress(Enclave.State) ->
     --#        ( not Admin.IsPresent(TheAdmin) and
     --#          not Admin.IsDoingOp(TheAdmin) ) );
   is

      ------------------------------------------------------------------
      -- ResetScreenMessage
      --
      -- Description:
      --    Resets the message on the screen based on the
      --    User Entry state and the Enclave state.
      --
      -- Implementation Notes:
      --    None
      --
      ------------------------------------------------------------------
      procedure ResetScreenMessage
        --# global in     Enclave.State;
        --#        in     UserEntry.State;
        --#        in     ConfigData.State;
        --#        in     Clock.Now;
        --#        in     TheAdmin;
        --#        in out AuditLog.State;
        --#        in out AuditLog.FileState;
        --#        in out Screen.State;
        --# derives Screen.State       from *,
        --#                                 UserEntry.State,
        --#                                 Enclave.State,
        --#                                 TheAdmin &
        --#         AuditLog.State,
        --#         AuditLog.FileState from Enclave.State,
        --#                                 UserEntry.State,
        --#                                 Screen.State,
        --#                                 AuditLog.State,
        --#                                 AuditLog.FileState,
        --#                                 ConfigData.State,
        --#                                 Clock.Now,
        --#                                 TheAdmin;
   is
      begin
         if UserEntry.InProgress then
            Screen.SetMessage(Msg => Screen.Busy);
         else
            Enclave.ResetScreenMessage(TheAdmin => TheAdmin);
         end if;
      end ResetScreenMessage;

   begin
      if Enclave.EnrolmentIsInProgress then
         Enclave.EnrolOp;
         --# check not Enclave.prf_statusIsWaitingStartAdminOp(Enclave.State) and
         --#       not Enclave.prf_statusIsWaitingFinishAdminOp(Enclave.State) and
         --#       not Enclave.prf_statusIsShutdown(Enclave.State);

      elsif Enclave.AdminMustLogout( TheAdmin => TheAdmin) then
         Enclave.AdminLogout( TheAdmin => TheAdmin);
         ResetScreenMessage;
         --# check not Admin.IsPresent (TheAdmin);

      elsif UserEntry.CurrentActivityPossible then
         UserEntry.Progress( TheStats => TheStats);
         ResetScreenMessage;

      elsif Enclave.CurrentAdminActivityPossible then
         Enclave.ProgressAdminActivity( TheAdmin => TheAdmin);

      elsif UserEntry.CanStart then
         UserEntry.StartEntry;
         ResetScreenMessage;

      else
         Enclave.StartAdminActivity( TheAdmin => TheAdmin);
      end if;
   end Processing;


   ------------------------------------------------------------------
   -- MainLoopBody
   --
   -- Description:
   --    Performs the TIS Main loop activities.
   --
   -- Traceunit: C.TIS.MainLoopBody
   -- Traceto: FD.TIS.TISMainLoop
   ------------------------------------------------------------------
   procedure MainLoopBody
     --# global in     Keyboard.Input;
     --#        in     Floppy.Input;
     --#        in     Door.Input;
     --#        in     Clock.Now;
     --#        in     AdminToken.Input;
     --#        in     Bio.Input;
     --#        in     UserToken.Input;
     --#        in out Door.State;
     --#        in out AuditLog.FileState;
     --#        in out UserToken.Status;
     --#        in out CertificateStore.FileState;
     --#        in out UserEntry.State;
     --#        in out Latch.State;
     --#        in out Enclave.State;
     --#        in out ConfigData.State;
     --#        in out AuditLog.State;
     --#        in out Display.State;
     --#        in out UserToken.State;
     --#        in out CertificateStore.State;
     --#        in out AdminToken.State;
     --#        in out ConfigData.FileState;
     --#        in out AdminToken.Status;
     --#        in out KeyStore.Store;
     --#        in out KeyStore.State;
     --#        in out Screen.State;
     --#        in out Floppy.WrittenState;
     --#        in out Floppy.State;
     --#        in out TheAdmin;
     --#        in out TheStats;
     --#           out Latch.Output;
     --#           out Alarm.Output;
     --#           out Display.Output;
     --#           out Clock.CurrentTime;
     --#           out UserToken.Output;
     --#           out Floppy.Output;
     --#           out Screen.Output;
     --#           out SystemFault;
     --# derives Door.State,
     --#         Latch.State,
     --#         Latch.Output,
     --#         SystemFault                from Door.State,
     --#                                         UserToken.Status,
     --#                                         UserEntry.State,
     --#                                         Latch.State,
     --#                                         Enclave.State,
     --#                                         ConfigData.State,
     --#                                         UserToken.State,
     --#                                         AdminToken.State,
     --#                                         AdminToken.Status,
     --#                                         Door.Input,
     --#                                         Clock.Now,
     --#                                         AdminToken.Input,
     --#                                         UserToken.Input,
     --#                                         TheAdmin &
     --#         AuditLog.FileState,
     --#         Alarm.Output,
     --#         AuditLog.State,
     --#         Screen.State,
     --#         Screen.Output              from Door.State,
     --#                                         AuditLog.FileState,
     --#                                         UserToken.Status,
     --#                                         CertificateStore.FileState,
     --#                                         UserEntry.State,
     --#                                         Latch.State,
     --#                                         Enclave.State,
     --#                                         ConfigData.State,
     --#                                         AuditLog.State,
     --#                                         Display.State,
     --#                                         UserToken.State,
     --#                                         CertificateStore.State,
     --#                                         AdminToken.State,
     --#                                         ConfigData.FileState,
     --#                                         AdminToken.Status,
     --#                                         KeyStore.Store,
     --#                                         KeyStore.State,
     --#                                         Screen.State,
     --#                                         Floppy.WrittenState,
     --#                                         Floppy.State,
     --#                                         Keyboard.Input,
     --#                                         Floppy.Input,
     --#                                         Door.Input,
     --#                                         Clock.Now,
     --#                                         AdminToken.Input,
     --#                                         Bio.Input,
     --#                                         UserToken.Input,
     --#                                         TheAdmin,
     --#                                         TheStats &
     --#         UserToken.Status,
     --#         CertificateStore.FileState,
     --#         CertificateStore.State     from *,
     --#                                         UserToken.Status,
     --#                                         UserEntry.State,
     --#                                         Latch.State,
     --#                                         Enclave.State,
     --#                                         ConfigData.State,
     --#                                         UserToken.State,
     --#                                         CertificateStore.State,
     --#                                         AdminToken.State,
     --#                                         AdminToken.Status,
     --#                                         KeyStore.Store,
     --#                                         KeyStore.State,
     --#                                         Door.Input,
     --#                                         Clock.Now,
     --#                                         AdminToken.Input,
     --#                                         UserToken.Input,
     --#                                         TheAdmin &
     --#         ConfigData.State,
     --#         ConfigData.FileState       from *,
     --#                                         UserToken.Status,
     --#                                         UserEntry.State,
     --#                                         Latch.State,
     --#                                         Enclave.State,
     --#                                         UserToken.State,
     --#                                         AdminToken.State,
     --#                                         AdminToken.Status,
     --#                                         Floppy.State,
     --#                                         Door.Input,
     --#                                         Clock.Now,
     --#                                         AdminToken.Input,
     --#                                         UserToken.Input,
     --#                                         TheAdmin &
     --#         Display.Output,
     --#         Display.State              from Door.State,
     --#                                         UserToken.Status,
     --#                                         UserEntry.State,
     --#                                         Latch.State,
     --#                                         Enclave.State,
     --#                                         ConfigData.State,
     --#                                         Display.State,
     --#                                         UserToken.State,
     --#                                         CertificateStore.State,
     --#                                         AdminToken.State,
     --#                                         AdminToken.Status,
     --#                                         KeyStore.Store,
     --#                                         KeyStore.State,
     --#                                         Floppy.State,
     --#                                         Door.Input,
     --#                                         Clock.Now,
     --#                                         AdminToken.Input,
     --#                                         Bio.Input,
     --#                                         UserToken.Input,
     --#                                         TheAdmin &
     --#         KeyStore.Store,
     --#         KeyStore.State             from *,
     --#                                         Latch.State,
     --#                                         Enclave.State,
     --#                                         KeyStore.Store,
     --#                                         Floppy.State,
     --#                                         Door.Input,
     --#                                         Clock.Now &
     --#         UserEntry.State            from *,
     --#                                         UserToken.Status,
     --#                                         Latch.State,
     --#                                         Enclave.State,
     --#                                         ConfigData.State,
     --#                                         UserToken.State,
     --#                                         AdminToken.State,
     --#                                         AdminToken.Status,
     --#                                         KeyStore.Store,
     --#                                         KeyStore.State,
     --#                                         Door.Input,
     --#                                         Clock.Now,
     --#                                         AdminToken.Input,
     --#                                         Bio.Input,
     --#                                         UserToken.Input,
     --#                                         TheAdmin &
     --#         Enclave.State              from *,
     --#                                         Door.State,
     --#                                         UserToken.Status,
     --#                                         UserEntry.State,
     --#                                         Latch.State,
     --#                                         UserToken.State,
     --#                                         AdminToken.State,
     --#                                         AdminToken.Status,
     --#                                         KeyStore.Store,
     --#                                         KeyStore.State,
     --#                                         Floppy.State,
     --#                                         Keyboard.Input,
     --#                                         Door.Input,
     --#                                         Clock.Now,
     --#                                         AdminToken.Input,
     --#                                         UserToken.Input,
     --#                                         TheAdmin &
     --#         UserToken.State            from *,
     --#                                         Door.State,
     --#                                         UserToken.Status,
     --#                                         UserEntry.State,
     --#                                         Latch.State,
     --#                                         Enclave.State,
     --#                                         ConfigData.State,
     --#                                         CertificateStore.State,
     --#                                         AdminToken.State,
     --#                                         AdminToken.Status,
     --#                                         KeyStore.Store,
     --#                                         KeyStore.State,
     --#                                         Door.Input,
     --#                                         Clock.Now,
     --#                                         AdminToken.Input,
     --#                                         UserToken.Input,
     --#                                         TheAdmin &
     --#         Clock.CurrentTime          from Clock.Now &
     --#         AdminToken.State           from *,
     --#                                         Door.State,
     --#                                         UserToken.Status,
     --#                                         UserEntry.State,
     --#                                         Latch.State,
     --#                                         Enclave.State,
     --#                                         UserToken.State,
     --#                                         AdminToken.Status,
     --#                                         KeyStore.Store,
     --#                                         KeyStore.State,
     --#                                         Door.Input,
     --#                                         Clock.Now,
     --#                                         AdminToken.Input,
     --#                                         UserToken.Input,
     --#                                         TheAdmin &
     --#         AdminToken.Status          from *,
     --#                                         UserToken.Status,
     --#                                         UserEntry.State,
     --#                                         Latch.State,
     --#                                         Enclave.State,
     --#                                         UserToken.State,
     --#                                         AdminToken.State,
     --#                                         Door.Input,
     --#                                         Clock.Now,
     --#                                         AdminToken.Input,
     --#                                         UserToken.Input,
     --#                                         TheAdmin &
     --#         UserToken.Output           from UserToken.Status,
     --#                                         UserEntry.State,
     --#                                         Latch.State,
     --#                                         Enclave.State,
     --#                                         ConfigData.State,
     --#                                         UserToken.State,
     --#                                         CertificateStore.State,
     --#                                         AdminToken.State,
     --#                                         AdminToken.Status,
     --#                                         KeyStore.Store,
     --#                                         KeyStore.State,
     --#                                         Door.Input,
     --#                                         Clock.Now,
     --#                                         AdminToken.Input,
     --#                                         UserToken.Input,
     --#                                         TheAdmin &
     --#         Floppy.Output              from Door.State,
     --#                                         AuditLog.FileState,
     --#                                         UserToken.Status,
     --#                                         UserEntry.State,
     --#                                         Latch.State,
     --#                                         Enclave.State,
     --#                                         ConfigData.State,
     --#                                         AuditLog.State,
     --#                                         Display.State,
     --#                                         UserToken.State,
     --#                                         AdminToken.State,
     --#                                         AdminToken.Status,
     --#                                         Floppy.State,
     --#                                         Door.Input,
     --#                                         Clock.Now,
     --#                                         AdminToken.Input,
     --#                                         UserToken.Input,
     --#                                         TheAdmin &
     --#         Floppy.WrittenState        from *,
     --#                                         Door.State,
     --#                                         AuditLog.FileState,
     --#                                         UserToken.Status,
     --#                                         UserEntry.State,
     --#                                         Latch.State,
     --#                                         Enclave.State,
     --#                                         ConfigData.State,
     --#                                         AuditLog.State,
     --#                                         Display.State,
     --#                                         UserToken.State,
     --#                                         AdminToken.State,
     --#                                         AdminToken.Status,
     --#                                         Floppy.State,
     --#                                         Door.Input,
     --#                                         Clock.Now,
     --#                                         AdminToken.Input,
     --#                                         UserToken.Input,
     --#                                         TheAdmin &
     --#         Floppy.State               from *,
     --#                                         UserToken.Status,
     --#                                         UserEntry.State,
     --#                                         Latch.State,
     --#                                         Enclave.State,
     --#                                         UserToken.State,
     --#                                         AdminToken.State,
     --#                                         AdminToken.Status,
     --#                                         Floppy.Input,
     --#                                         Door.Input,
     --#                                         Clock.Now,
     --#                                         AdminToken.Input,
     --#                                         UserToken.Input,
     --#                                         TheAdmin &
     --#         TheAdmin                   from *,
     --#                                         Door.State,
     --#                                         UserToken.Status,
     --#                                         UserEntry.State,
     --#                                         Latch.State,
     --#                                         Enclave.State,
     --#                                         UserToken.State,
     --#                                         AdminToken.State,
     --#                                         AdminToken.Status,
     --#                                         KeyStore.Store,
     --#                                         KeyStore.State,
     --#                                         Keyboard.Input,
     --#                                         Door.Input,
     --#                                         Clock.Now,
     --#                                         AdminToken.Input,
     --#                                         UserToken.Input &
     --#         TheStats                   from *,
     --#                                         UserToken.Status,
     --#                                         UserEntry.State,
     --#                                         Latch.State,
     --#                                         Enclave.State,
     --#                                         ConfigData.State,
     --#                                         UserToken.State,
     --#                                         AdminToken.State,
     --#                                         AdminToken.Status,
     --#                                         Door.Input,
     --#                                         Clock.Now,
     --#                                         AdminToken.Input,
     --#                                         Bio.Input,
     --#                                         UserToken.Input,
     --#                                         TheAdmin;
     --# pre  (not Enclave.EnrolmentIsInProgress(Enclave.State) <->
     --#             KeyStore.PrivateKeyPresent(KeyStore.State)) and
     --#
     --#      Latch.IsLocked(Latch.State) = Latch.prf_isLocked(Latch.Output) and
     --#
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
     --#      ( ( Admin.IsDoingOp(TheAdmin) and
     --#          Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp ) ->
     --#                    Enclave.prf_statusIsWaitingStartAdminOp(Enclave.State) ) and
     --#
     --#      ( ( Enclave.prf_statusIsGotAdminToken(Enclave.State) or
     --#          Enclave.prf_statusIsWaitingRemoveAdminTokenFail(Enclave.State) ) ->
     --#        not Admin.IsPresent(TheAdmin) ) and
     --#
     --#      ( ( Enclave.prf_statusIsWaitingStartAdminOp(Enclave.State) or
     --#          Enclave.prf_statusIsWaitingFinishAdminOp(Enclave.State) ) ->
     --#        ( Admin.IsPresent(TheAdmin) and
     --#          Admin.IsDoingOp(TheAdmin) ) ) and
     --#
     --#      ( Enclave.prf_statusIsEnclaveQuiescent(Enclave.State) ->
     --#        not Admin.IsDoingOp(TheAdmin) ) and
     --#
     --#      ( Enclave.prf_statusIsShutdown(Enclave.State) ->
     --#        ( not Admin.IsDoingOp(TheAdmin) and
     --#          Admin.prf_rolePresent(TheAdmin) = PrivTypes.UserOnly ) ) and
     --#
     --#      ( Enclave.EnrolmentIsInProgress(Enclave.State) ->
     --#        ( not Admin.IsPresent(TheAdmin) and
     --#          not Admin.IsDoingOp(TheAdmin) ) );
     --#
     --#
     --# post ( not Enclave.EnrolmentIsInProgress(Enclave.State) <->
     --#             KeyStore.PrivateKeyPresent(KeyStore.State) ) and
     --#
     --#      ( Latch.IsLocked(Latch.State) = Latch.prf_isLocked(Latch.Output)
     --#        or SystemFault
     --#      ) and
     --#
     --#      -------------------------------------------------------
     --#      -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3         --
     --#      --===================================================--
     --#      -- After each call to MainLoopBody, either the       --
     --#      -- security property holds, or a critical system     --
     --#      -- fault has occurred, in which case the TIS will be --
     --#      -- shutdown                                          --
     --#      -------------------------------------------------------
     --#      ( ( Latch.IsLocked(Latch.State) and
     --#          Door.TheCurrentDoor(Door.State) = Door.Open and
     --#          Clock.GreaterThanOrEqual(Clock.TheCurrentTime(Clock.CurrentTime),
     --#                                   Door.prf_alarmTimeout(Door.State)) ) ->
     --#        ( Alarm.prf_isAlarming(Alarm.Output) or SystemFault ) ) and
     --#
     --#
     --#
     --#      ( ( ( Latch.prf_isLocked(Latch.Output~) and
     --#            not Latch.prf_isLocked(Latch.Output) and
     --#            not Latch.IsLocked(Latch.State) and
     --#            Latch.IsLocked(Latch.State~) = Latch.prf_isLocked(Latch.Output~)
     --#          )
     --#          ->
     --#          ( UserEntry.prf_UserEntryUnlockDoor or
     --#            ( AdminToken.prf_isGood(AdminToken.State) and
     --#              AdminToken.prf_authCertValid(AdminToken.State) and
     --#              AdminToken.TheAuthCertRole(AdminToken.State) = PrivTypes.Guard )
     --#          )
     --#        )
     --#        or SystemFault
     --#      ) and
     --#
     --#      ( Admin.prf_rolePresent(TheAdmin) = PrivTypes.Guard ->
     --#           ( AdminToken.prf_isGood(AdminToken.State) and
     --#             AdminToken.prf_authCertValid(AdminToken.State) and
     --#             AdminToken.TheAuthCertRole(AdminToken.State) = PrivTypes.Guard )) and
     --#
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
     --#      ( ( Admin.IsDoingOp(TheAdmin) and
     --#          Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp ) ->
     --#                    Enclave.prf_statusIsWaitingStartAdminOp(Enclave.State) ) and
     --#
     --#      ( ( Enclave.prf_statusIsGotAdminToken(Enclave.State) or
     --#          Enclave.prf_statusIsWaitingRemoveAdminTokenFail(Enclave.State) ) ->
     --#        not Admin.IsPresent(TheAdmin) ) and
     --#
     --#      ( ( Enclave.prf_statusIsWaitingStartAdminOp(Enclave.State) or
     --#          Enclave.prf_statusIsWaitingFinishAdminOp(Enclave.State) ) ->
     --#        ( Admin.IsDoingOp(TheAdmin) and
     --#          Admin.IsPresent(TheAdmin) and
     --#          Admin.prf_rolePresent(TheAdmin) = Admin.prf_rolePresent(TheAdmin~) ) ) and
     --#
     --#      ( Enclave.prf_statusIsEnclaveQuiescent(Enclave.State) ->
     --#        ( not Admin.IsDoingOp(TheAdmin) ) ) and
     --#
     --#      ( Enclave.prf_statusIsShutdown(Enclave.State) ->
     --#        ( not Admin.IsDoingOp(TheAdmin) and
     --#          Admin.prf_rolePresent(TheAdmin) = PrivTypes.UserOnly ) ) and
     --#
     --#      ( Enclave.EnrolmentIsInProgress(Enclave.State) ->
     --#        ( not Admin.IsPresent(TheAdmin) and
     --#          not Admin.IsDoingOp(TheAdmin) ) );
   is


      --------------------------------------------------------------
      -- begin MainLoopBody
      --------------------------------------------------------------
   begin
      Poll.Activity(SystemFault => SystemFault);

      if not SystemFault then
         Updates.EarlyActivity(SystemFault => SystemFault);

         if not SystemFault then

            Processing;

            Updates.Activity(SystemFault => SystemFault,
                             TheStats    => TheStats,
                             TheAdmin    => TheAdmin);

         end if;
      end if;
   end MainLoopBody;


   ------------------------------------------------------------------
   -- ShutdownDoorLatchFailure
   --
   -- Description:
   --    Puts the system into a safe state and updates the outputs following
   --    a failure in the Door or Latch.
   --
   -- Traceunit: C.TIS.ShutdownDoorLatchFailure
   -- Traceto:
   ------------------------------------------------------------------
   procedure ShutdownDoorLatchFailure
     --# global in     ConfigData.State;
     --#        in     Clock.Now;
     --#        in     TheStats;
     --#        in out AuditLog.FileState;
     --#        in out AuditLog.State;
     --#        in out Display.State;
     --#        in out Screen.State;
     --#           out Door.State;
     --#           out Latch.State;
     --#           out Latch.Output;
     --#           out Alarm.Output;
     --#           out Display.Output;
     --#           out Screen.Output;
     --#           out TheAdmin;
     --# derives Door.State,
     --#         Latch.State,
     --#         Latch.Output,
     --#         TheAdmin           from  &
     --#         AuditLog.FileState,
     --#         Alarm.Output,
     --#         AuditLog.State,
     --#         Screen.State,
     --#         Screen.Output      from AuditLog.FileState,
     --#                                 ConfigData.State,
     --#                                 AuditLog.State,
     --#                                 Display.State,
     --#                                 Screen.State,
     --#                                 Clock.Now,
     --#                                 TheStats &
     --#         Display.State,
     --#         Display.Output     from Display.State;
   is

      UnusedFault : Boolean;

   begin
      Door.Failure;
      Admin.Logout(TheAdmin => TheAdmin);

      --# accept F, 10, UnusedFault, "Ineffective assignment expected here" &
      --#        F, 33, UnusedFault, "Ineffective assignment expected here";
      Updates.Activity(SystemFault => UnusedFault,
                       TheStats    => TheStats,
                       TheAdmin    => TheAdmin);
   end ShutdownDoorLatchFailure;


   ------------------------------------------------------------------
   -- ShutdownAuditLogFailure
   --
   -- Description:
   --    Puts the system into a safe state and updates the outputs following
   --    a failure to write to the audit log.
   --
   -- Traceunit: C.TIS.ShutdownAuditLogFailure
   -- Traceto:
   ------------------------------------------------------------------
   procedure ShutdownAuditLogFailure
     --# global in     ConfigData.State;
     --#        in     Clock.CurrentTime;
     --#        in     Clock.Now;
     --#        in     TheStats;
     --#        in out Display.State;
     --#        in out Door.State;
     --#        in out AuditLog.FileState;
     --#        in out Latch.State;
     --#        in out AuditLog.State;
     --#        in out Screen.State;
     --#           out Latch.Output;
     --#           out Alarm.Output;
     --#           out Display.Output;
     --#           out Screen.Output;
     --#           out TheAdmin;
     --# derives Door.State,
     --#         Latch.State        from *,
     --#                                 Latch.State,
     --#                                 Clock.CurrentTime &
     --#         AuditLog.FileState,
     --#         Alarm.Output,
     --#         AuditLog.State,
     --#         Screen.State,
     --#         Screen.Output      from Door.State,
     --#                                 AuditLog.FileState,
     --#                                 Latch.State,
     --#                                 ConfigData.State,
     --#                                 AuditLog.State,
     --#                                 Display.State,
     --#                                 Clock.CurrentTime,
     --#                                 Screen.State,
     --#                                 Clock.Now,
     --#                                 TheStats &
     --#         Latch.Output       from Latch.State,
     --#                                 Clock.CurrentTime &
     --#         Display.State,
     --#         Display.Output     from Display.State &
     --#         TheAdmin           from ;
   is

      UnusedFault : Boolean;

   begin
      Door.LockDoor;
      Admin.Logout(TheAdmin => TheAdmin);

      --# accept F, 10, UnusedFault, "Ineffective assignment expected here" &
      --#        F, 33, UnusedFault, "Ineffective assignment expected here";
      Updates.Activity(SystemFault => UnusedFault,
                       TheStats    => TheStats,
                       TheAdmin    => TheAdmin);
   end ShutdownAuditLogFailure;

begin

   Init;

   loop

      --# assert ( not Enclave.EnrolmentIsInProgress(Enclave.State) <->
      --#             KeyStore.PrivateKeyPresent(KeyStore.State) ) and
      --#
      --#      Latch.State = prf_preLatchState and
      --#      Latch.Output = prf_preLatchOutput and
      --#      Latch.IsLocked(Latch.State) = Latch.prf_isLocked(Latch.Output) and
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
      --#      ( ( Admin.IsDoingOp(TheAdmin) and
      --#          Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp ) ->
      --#                    Enclave.prf_statusIsWaitingStartAdminOp(Enclave.State) ) and
      --#
      --#      ( ( Enclave.prf_statusIsGotAdminToken(Enclave.State) or
      --#          Enclave.prf_statusIsWaitingRemoveAdminTokenFail(Enclave.State) ) ->
      --#        not Admin.IsPresent(TheAdmin) ) and
      --#
      --#      ( ( Enclave.prf_statusIsWaitingStartAdminOp(Enclave.State) or
      --#          Enclave.prf_statusIsWaitingFinishAdminOp(Enclave.State) ) ->
      --#        ( Admin.IsPresent(TheAdmin) and
      --#          Admin.IsDoingOp(TheAdmin) ) ) and
      --#
      --#      ( Enclave.prf_statusIsEnclaveQuiescent(Enclave.State) ->
      --#        not Admin.IsDoingOp(TheAdmin) ) and
      --#
      --#      ( Enclave.prf_statusIsShutdown(Enclave.State) ->
      --#        ( not Admin.IsDoingOp(TheAdmin) and
      --#          Admin.prf_rolePresent(TheAdmin) = PrivTypes.UserOnly ) ) and
      --#
      --#      ( Enclave.EnrolmentIsInProgress(Enclave.State) ->
      --#        ( not Admin.IsPresent(TheAdmin) and
      --#          not Admin.IsDoingOp(TheAdmin) ) );

      MainLoopBody;

      ShutdownCompleted := Enclave.HasShutdown;

      exit when ShutdownCompleted;

      --# assert
      --#      not ShutdownCompleted and
      --#      ( not Enclave.EnrolmentIsInProgress(Enclave.State) <->
      --#             KeyStore.PrivateKeyPresent(KeyStore.State) ) and
      --#
      --#      -------------------------------------------------------
      --#      -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3         --
      --#      --===================================================--
      --#      -- After each cycle of the TIS main loop, either the --
      --#      -- security property holds, or a critical system     --
      --#      -- fault has occurred, in which case the TIS will be --
      --#      -- shutdown                                          --
      --#      -------------------------------------------------------
      --#
      --#      ( ( Latch.IsLocked(Latch.State) and
      --#          Door.TheCurrentDoor(Door.State) = Door.Open and
      --#          Clock.GreaterThanOrEqual(Clock.TheCurrentTime(Clock.CurrentTime),
      --#                                   Door.prf_alarmTimeout(Door.State)) ) ->
      --#        ( Alarm.prf_isAlarming(Alarm.Output) or SystemFault ) ) and
      --#
      --#
      --#      ( ( ( Latch.prf_isLocked(prf_preLatchOutput) and
      --#            not Latch.prf_isLocked(Latch.Output) and
      --#            Latch.IsLocked(prf_preLatchState) = Latch.prf_isLocked(prf_preLatchOutput)
      --#          )
      --#          ->
      --#          ( UserEntry.prf_UserEntryUnlockDoor or
      --#            ( AdminToken.prf_isGood(AdminToken.State) and
      --#              AdminToken.prf_authCertValid(AdminToken.State) and
      --#              AdminToken.TheAuthCertRole(AdminToken.State) = PrivTypes.Guard )
      --#          )
      --#        )
      --#        or SystemFault
      --#      ) and
      --#
      --#      ( Latch.IsLocked(Latch.State) = Latch.prf_isLocked(Latch.Output)
      --#        or SystemFault
      --#      ) and
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
      --#      ( ( Admin.IsDoingOp(TheAdmin) and
      --#          Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp ) ->
      --#                    Enclave.prf_statusIsWaitingStartAdminOp(Enclave.State) ) and
      --#
      --#      ( ( Enclave.prf_statusIsGotAdminToken(Enclave.State) or
      --#          Enclave.prf_statusIsWaitingRemoveAdminTokenFail(Enclave.State) ) ->
      --#        not Admin.IsPresent(TheAdmin) ) and
      --#
      --#      ( ( Enclave.prf_statusIsWaitingStartAdminOp(Enclave.State) or
      --#          Enclave.prf_statusIsWaitingFinishAdminOp(Enclave.State) ) ->
      --#        ( Admin.IsDoingOp(TheAdmin) and
      --#          Admin.IsPresent(TheAdmin) ) ) and
      --#
      --#      ( Enclave.prf_statusIsEnclaveQuiescent(Enclave.State) ->
      --#        ( not Admin.IsDoingOp(TheAdmin) ) ) and
      --#
      --#      ( Enclave.prf_statusIsShutdown(Enclave.State) ->
      --#        ( not Admin.IsDoingOp(TheAdmin) and
      --#          Admin.prf_rolePresent(TheAdmin) = PrivTypes.UserOnly ) ) and
      --#
      --#      ( Enclave.EnrolmentIsInProgress(Enclave.State) ->
      --#        ( not Admin.IsPresent(TheAdmin) and
      --#          not Admin.IsDoingOp(TheAdmin) ) );

      if SystemFault then
         --# accept F, 10, TheAdmin, "Ineffective assignmente expected here";
         ShutdownDoorLatchFailure;
         --# end accept;
         exit;
      end if;

      if AuditLog.SystemFaultOccurred then
         --# accept F, 10, TheAdmin, "Ineffective assignmente expected here";
         ShutdownAuditLogFailure;
         --# end accept;
         exit;
      end if;

      --# assert
      --#      not ShutdownCompleted and not SystemFault and
      --#
      --#      ( not Enclave.EnrolmentIsInProgress(Enclave.State) <->
      --#             KeyStore.PrivateKeyPresent(KeyStore.State) ) and
      --#
      --#      -------------------------------------------------------
      --#      -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3         --
      --#      --===================================================--
      --#      -- After each cycle of the TIS main loop, either the --
      --#      -- security property holds, or a critical system     --
      --#      -- fault has occurred, in which case the TIS will be --
      --#      -- shutdown                                          --
      --#      -------------------------------------------------------
      --#
      --#      ( ( Latch.IsLocked(Latch.State) and
      --#          Door.TheCurrentDoor(Door.State) = Door.Open and
      --#          Clock.GreaterThanOrEqual(Clock.TheCurrentTime(Clock.CurrentTime),
      --#                                   Door.prf_alarmTimeout(Door.State)) ) ->
      --#        ( Alarm.prf_isAlarming(Alarm.Output) or SystemFault ) ) and
      --#
      --#
      --#      ( ( Latch.prf_isLocked(prf_preLatchOutput) and
      --#          not Latch.prf_isLocked(Latch.Output) and
      --#          Latch.IsLocked(prf_preLatchState) = Latch.prf_isLocked(prf_preLatchOutput)
      --#        )
      --#        ->
      --#        ( UserEntry.prf_UserEntryUnlockDoor or
      --#          ( AdminToken.prf_isGood(AdminToken.State) and
      --#            AdminToken.prf_authCertValid(AdminToken.State) and
      --#            AdminToken.TheAuthCertRole(AdminToken.State) = PrivTypes.Guard )
      --#        )
      --#      ) and
      --#
      --#      ( Latch.IsLocked(Latch.State) = Latch.prf_isLocked(Latch.Output)
      --#        or SystemFault
      --#      ) and
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
      --#      ( ( Admin.IsDoingOp(TheAdmin) and
      --#          Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp ) ->
      --#                    Enclave.prf_statusIsWaitingStartAdminOp(Enclave.State) ) and
      --#
      --#      ( ( Enclave.prf_statusIsGotAdminToken(Enclave.State) or
      --#          Enclave.prf_statusIsWaitingRemoveAdminTokenFail(Enclave.State) ) ->
      --#        not Admin.IsPresent(TheAdmin) ) and
      --#
      --#      ( ( Enclave.prf_statusIsWaitingStartAdminOp(Enclave.State) or
      --#          Enclave.prf_statusIsWaitingFinishAdminOp(Enclave.State) ) ->
      --#        ( Admin.IsDoingOp(TheAdmin) and
      --#          Admin.IsPresent(TheAdmin) ) ) and
      --#
      --#      ( Enclave.prf_statusIsEnclaveQuiescent(Enclave.State) ->
      --#        ( not Admin.IsDoingOp(TheAdmin) ) ) and
      --#
      --#      ( Enclave.prf_statusIsShutdown(Enclave.State) ->
      --#        ( not Admin.IsDoingOp(TheAdmin) and
      --#          Admin.prf_rolePresent(TheAdmin) = PrivTypes.UserOnly ) ) and
      --#
      --#      ( Enclave.EnrolmentIsInProgress(Enclave.State) ->
      --#        ( not Admin.IsPresent(TheAdmin) and
      --#          not Admin.IsDoingOp(TheAdmin) ) );

   end loop;

   Keyboard.Finalise;

end TISMain;

