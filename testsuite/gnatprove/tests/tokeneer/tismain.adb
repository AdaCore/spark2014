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
-- TIS main program
--
-- Description:
--    The TIS main program
--
-- Implementation Notes:
--    None.
------------------------------------------------------------------
with Admin,
     AdminToken,
     Alarm,
     AlarmTypes,
     AuditLog,
     AuditTypes,
     Bio,
     CertificateStore,
     Clock,
     Configuration,
     ConfigData,
     Door,
     Display,
     Enclave,
     Floppy,
     Keyboard,
     KeyStore,
     Latch,
     Poll,
     PrivTypes,
     Screen,
     Stats,
     UserEntry,
     UserToken,
     Updates;

use Admin,
    AlarmTypes,
    Clock,
    Door,
    PrivTypes;

procedure TISMain
  with Global  => (Input  => (AdminToken.Input,
                              Bio.Input,
                              Clock.Now,
                              Door.Input,
                              Floppy.Input,
                              Keyboard.Inputs,
                              UserToken.Input),
                   Output => (AdminToken.State,
                              AuditLog.State,
                              CertificateStore.State,
                              Clock.CurrentTime,
                              ConfigData.State,
                              Display.State,
                              Door.State,
                              Enclave.State,
                              Floppy.State,
                              Floppy.WrittenState,
                              KeyStore.State,
                              Latch.State,
                              Screen.Output,
                              Screen.State,
                              UserToken.State),
                   In_Out => (AdminToken.Status,
                              Alarm.Output,
                              AuditLog.FileState,
                              CertificateStore.FileState,
                              ConfigData.FileState,
                              Display.Output,
                              Floppy.Output,
                              KeyStore.Store,
                              Latch.Output,
                              UserEntry.State,
                              UserToken.Output,
                              UserToken.Status)),
       Depends => ((Alarm.Output,
                    Display.Output,
                    Floppy.Output,
                    Latch.Output,
                    UserToken.Output)          =>+ (AdminToken.Input,
                                                    AdminToken.Status,
                                                    AuditLog.FileState,
                                                    Bio.Input,
                                                    CertificateStore.FileState,
                                                    Clock.Now,
                                                    ConfigData.FileState,
                                                    Door.Input,
                                                    Floppy.Input,
                                                    Keyboard.Inputs,
                                                    KeyStore.Store,
                                                    UserEntry.State,
                                                    UserToken.Input,
                                                    UserToken.Status),
                   (AdminToken.State,
                    AdminToken.Status,
                    AuditLog.FileState,
                    AuditLog.State,
                    CertificateStore.FileState,
                    CertificateStore.State,
                    Clock.CurrentTime,
                    ConfigData.FileState,
                    ConfigData.State,
                    Display.State,
                    Door.State,
                    Enclave.State,
                    Floppy.State,
                    Floppy.WrittenState,
                    KeyStore.State,
                    KeyStore.Store,
                    Latch.State,
                    Screen.Output,
                    Screen.State,
                    UserEntry.State,
                    UserToken.State,
                    UserToken.Status)           => (AdminToken.Input,
                                                    AdminToken.Status,
                                                    AuditLog.FileState,
                                                    Bio.Input,
                                                    CertificateStore.FileState,
                                                    Clock.Now,
                                                    ConfigData.FileState,
                                                    Door.Input,
                                                    Floppy.Input,
                                                    Keyboard.Inputs,
                                                    KeyStore.Store,
                                                    UserEntry.State,
                                                    UserToken.Input,
                                                    UserToken.Status))
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
     with Global  => (Input  => (Clock.Now,
                                 Keyboard.Inputs,
                                 KeyStore.Store),
                      Output => (AdminToken.State,
                                 AuditLog.State,
                                 CertificateStore.State,
                                 ConfigData.State,
                                 Display.State,
                                 Door.State,
                                 Enclave.State,
                                 Floppy.State,
                                 Floppy.WrittenState,
                                 KeyStore.State,
                                 Latch.State,
                                 Screen.Output,
                                 Screen.State,
                                 TheAdmin,
                                 TheStats,
                                 UserToken.State),
                      In_Out => (AdminToken.Status,
                                 AuditLog.FileState,
                                 CertificateStore.FileState,
                                 ConfigData.FileState,
                                 UserToken.Status)),
          Depends => ((AdminToken.State,
                       AdminToken.Status) => AdminToken.Status,

                      (AuditLog.FileState,
                       AuditLog.State) => (AuditLog.FileState,
                                           CertificateStore.FileState,
                                           Clock.Now,
                                           ConfigData.FileState,
                                           KeyStore.Store,
                                           UserToken.Status),

                      (CertificateStore.FileState,
                       ConfigData.FileState,
                       UserToken.Status) =>+ null,

                      CertificateStore.State => CertificateStore.FileState,

                      ConfigData.State => ConfigData.FileState,

                      (Display.State,
                       Enclave.State,
                       KeyStore.State,
                       Screen.Output,
                       Screen.State) => KeyStore.Store,

                      (Door.State,
                       Floppy.State,
                       Floppy.WrittenState,
                       Latch.State,
                       TheAdmin,
                       TheStats) => null,

                      UserToken.State => UserToken.Status,

                      null => Keyboard.Inputs),
          Post    => ((not Enclave.EnrolmentIsInProgress) =
                        KeyStore.PrivateKeyPresent) and

                     (Enclave.EnrolmentIsInProgress or
                        Enclave.statusIsEnclaveQuiescent) and

                     not Admin.IsPresent(TheAdmin) and
                     not Admin.IsDoingOp(TheAdmin) and

                     Admin.RolePresent(TheAdmin) /= PrivTypes.Guard and

                     not Enclave.statusIsWaitingStartAdminOp and
                     not Enclave.statusIsWaitingFinishAdminOp and
                     not Enclave.statusIsShutdown and

                     not AdminToken.isGood and
                     not AdminToken.authCertValid and
                     AdminToken.TheAuthCertRole /= PrivTypes.Guard
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
           (ElementID   => AuditTypes.StartEnrolledTIS,
            Severity    => AuditTypes.Information,
            User        => AuditTypes.NoUser,
            Description => AuditTypes.NoDescription);

      else
         AuditLog.AddElementToLog
           (ElementID   => AuditTypes.StartUnenrolledTIS,
            Severity    => AuditTypes.Information,
            User        => AuditTypes.NoUser,
            Description => AuditTypes.NoDescription);

      end if;
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
     with Global  => (Input  => (AdminToken.Input,
                                 Bio.Input,
                                 Clock.CurrentTime,
                                 Clock.Now,
                                 Floppy.Input,
                                 Keyboard.Inputs,
                                 UserToken.Input),
                      In_Out => (AdminToken.State,
                                 AdminToken.Status,
                                 AuditLog.FileState,
                                 AuditLog.State,
                                 CertificateStore.FileState,
                                 CertificateStore.State,
                                 ConfigData.FileState,
                                 ConfigData.State,
                                 Display.State,
                                 Door.State,
                                 Enclave.State,
                                 Floppy.Output,
                                 Floppy.State,
                                 Floppy.WrittenState,
                                 KeyStore.State,
                                 KeyStore.Store,
                                 Latch.State,
                                 Screen.State,
                                 TheAdmin,
                                 TheStats,
                                 UserEntry.State,
                                 UserToken.Output,
                                 UserToken.State,
                                 UserToken.Status)),
          Depends => (AdminToken.State =>+ (AdminToken.Input,
                                            AdminToken.Status,
                                            Clock.CurrentTime,
                                            Door.State,
                                            Enclave.State,
                                            KeyStore.State,
                                            KeyStore.Store,
                                            TheAdmin,
                                            UserEntry.State,
                                            UserToken.State),

                      AdminToken.Status =>+ (AdminToken.State,
                                             Clock.CurrentTime,
                                             Enclave.State,
                                             TheAdmin,
                                             UserEntry.State,
                                             UserToken.State),

                      (AuditLog.FileState,
                       AuditLog.State) => (AdminToken.Input,
                                           AdminToken.State,
                                           AdminToken.Status,
                                           AuditLog.FileState,
                                           AuditLog.State,
                                           Bio.Input,
                                           CertificateStore.FileState,
                                           CertificateStore.State,
                                           Clock.CurrentTime,
                                           Clock.Now,
                                           ConfigData.FileState,
                                           ConfigData.State,
                                           Display.State,
                                           Door.State,
                                           Enclave.State,
                                           Floppy.Input,
                                           Floppy.State,
                                           Floppy.WrittenState,
                                           Keyboard.Inputs,
                                           KeyStore.State,
                                           KeyStore.Store,
                                           Latch.State,
                                           Screen.State,
                                           TheAdmin,
                                           UserEntry.State,
                                           UserToken.Input,
                                           UserToken.State,
                                           UserToken.Status),

                      (CertificateStore.FileState,
                       CertificateStore.State) =>+ (AdminToken.State,
                                                    CertificateStore.State,
                                                    Clock.CurrentTime,
                                                    ConfigData.State,
                                                    Enclave.State,
                                                    KeyStore.State,
                                                    KeyStore.Store,
                                                    TheAdmin,
                                                    UserEntry.State,
                                                    UserToken.State,
                                                    UserToken.Status),

                      (ConfigData.FileState,
                       ConfigData.State) =>+ (AdminToken.State,
                                              Clock.CurrentTime,
                                              Enclave.State,
                                              Floppy.State,
                                              TheAdmin,
                                              UserEntry.State,
                                              UserToken.State),

                      Display.State =>+ (AdminToken.State,
                                         Bio.Input,
                                         CertificateStore.State,
                                         Clock.CurrentTime,
                                         ConfigData.State,
                                         Door.State,
                                         Enclave.State,
                                         Floppy.State,
                                         KeyStore.State,
                                         KeyStore.Store,
                                         TheAdmin,
                                         UserEntry.State,
                                         UserToken.Input,
                                         UserToken.State,
                                         UserToken.Status),

                      (Door.State,
                       Latch.State) => (AdminToken.State,
                                        Clock.CurrentTime,
                                        ConfigData.State,
                                        Door.State,
                                        Enclave.State,
                                        Latch.State,
                                        TheAdmin,
                                        UserEntry.State,
                                        UserToken.State),

                      Enclave.State =>+ (AdminToken.Input,
                                         AdminToken.State,
                                         AdminToken.Status,
                                         Clock.CurrentTime,
                                         Door.State,
                                         Floppy.State,
                                         Keyboard.Inputs,
                                         KeyStore.State,
                                         KeyStore.Store,
                                         TheAdmin,
                                         UserEntry.State,
                                         UserToken.State),

                      Floppy.Output =>+ (AdminToken.State,
                                         AuditLog.FileState,
                                         AuditLog.State,
                                         Clock.CurrentTime,
                                         Enclave.State,
                                         Floppy.State,
                                         TheAdmin,
                                         UserEntry.State,
                                         UserToken.State),

                      Floppy.State =>+ (AdminToken.State,
                                        Clock.CurrentTime,
                                        Enclave.State,
                                        Floppy.Input,
                                        TheAdmin,
                                        UserEntry.State,
                                        UserToken.State),

                      Floppy.WrittenState =>+ (AdminToken.State,
                                               AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.CurrentTime,
                                               Enclave.State,
                                               Floppy.State,
                                               TheAdmin,
                                               UserEntry.State,
                                               UserToken.State),

                      (KeyStore.State,
                       KeyStore.Store) =>+ (Enclave.State,
                                            Floppy.State,
                                            KeyStore.Store),

                      Screen.State =>+ (AdminToken.Input,
                                        AdminToken.State,
                                        AdminToken.Status,
                                        Bio.Input,
                                        Clock.CurrentTime,
                                        ConfigData.State,
                                        Door.State,
                                        Enclave.State,
                                        Floppy.Input,
                                        Floppy.State,
                                        Floppy.WrittenState,
                                        Keyboard.Inputs,
                                        KeyStore.State,
                                        KeyStore.Store,
                                        TheAdmin,
                                        UserEntry.State,
                                        UserToken.Input,
                                        UserToken.State,
                                        UserToken.Status),

                      TheAdmin =>+ (AdminToken.Input,
                                    AdminToken.State,
                                    AdminToken.Status,
                                    Clock.CurrentTime,
                                    Door.State,
                                    Enclave.State,
                                    Keyboard.Inputs,
                                    KeyStore.State,
                                    KeyStore.Store,
                                    UserEntry.State,
                                    UserToken.State),

                      TheStats =>+ (AdminToken.State,
                                    Bio.Input,
                                    Clock.CurrentTime,
                                    ConfigData.State,
                                    Enclave.State,
                                    TheAdmin,
                                    UserEntry.State,
                                    UserToken.State),

                      UserEntry.State =>+ (AdminToken.State,
                                           Bio.Input,
                                           Clock.CurrentTime,
                                           ConfigData.State,
                                           Enclave.State,
                                           KeyStore.State,
                                           KeyStore.Store,
                                           TheAdmin,
                                           UserToken.Input,
                                           UserToken.State,
                                           UserToken.Status),

                      UserToken.Output =>+ (AdminToken.State,
                                            CertificateStore.State,
                                            Clock.CurrentTime,
                                            ConfigData.State,
                                            Enclave.State,
                                            KeyStore.State,
                                            KeyStore.Store,
                                            TheAdmin,
                                            UserEntry.State,
                                            UserToken.State,
                                            UserToken.Status),

                      UserToken.State =>+ (AdminToken.State,
                                           CertificateStore.State,
                                           Clock.CurrentTime,
                                           ConfigData.State,
                                           Door.State,
                                           Enclave.State,
                                           KeyStore.State,
                                           KeyStore.Store,
                                           TheAdmin,
                                           UserEntry.State,
                                           UserToken.Input,
                                           UserToken.Status),

                      UserToken.Status =>+ (AdminToken.State,
                                            CertificateStore.State,
                                            Clock.CurrentTime,
                                            ConfigData.State,
                                            Enclave.State,
                                            KeyStore.State,
                                            KeyStore.Store,
                                            TheAdmin,
                                            UserEntry.State,
                                            UserToken.Input,
                                            UserToken.State)),
          Pre     =>
     ((not Enclave.EnrolmentIsInProgress) =
        KeyStore.PrivateKeyPresent) and
          --------------------------------------------------------
          -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
          --====================================================--
          -- Before each call to Processing, the security       --
          -- property holds.                                    --
          --------------------------------------------------------
       ((Latch.IsLocked and
           Door.TheCurrentDoor = Door.Open and
           Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
                                    Door.alarm_Timeout)) =
          (Door.TheDoorAlarm = AlarmTypes.Alarming)) and

       (if Admin.RolePresent(TheAdmin) = PrivTypes.Guard then
           (AdminToken.isGood and
              AdminToken.authCertValid and
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

       (if (Admin.IsDoingOp(TheAdmin) and then
              Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp)
        then
           Enclave.statusIsWaitingStartAdminOp) and

       (if (Enclave.statusIsGotAdminToken or
              Enclave.statusIsWaitingRemoveAdminTokenFail)
        then
           not Admin.IsPresent(TheAdmin)) and

       (if (Enclave.statusIsWaitingStartAdminOp or
              Enclave.statusIsWaitingFinishAdminOp)
        then
           (Admin.IsPresent(TheAdmin) and
              Admin.IsDoingOp(TheAdmin))) and

       (if Enclave.statusIsEnclaveQuiescent then
           not Admin.IsDoingOp(TheAdmin)) and

       (if Enclave.statusIsShutdown then
           (not Admin.IsDoingOp(TheAdmin) and
              Admin.RolePresent(TheAdmin) = PrivTypes.UserOnly)) and

       (if Enclave.EnrolmentIsInProgress then
           (not Admin.IsPresent(TheAdmin) and
              not Admin.IsDoingOp(TheAdmin))),

          --------------------------------------------------------
          -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
          --====================================================--
          -- After each call to Processing, the security        --
          -- property holds.                                    --
          --------------------------------------------------------
          Post    =>
       ((not Enclave.EnrolmentIsInProgress) =
          KeyStore.PrivateKeyPresent) and

         ((Latch.IsLocked and
             Door.TheCurrentDoor = Door.Open and
             Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
                                      Door.alarm_Timeout)) =
            (Door.TheDoorAlarm = AlarmTypes.Alarming)) and

         (if (Admin.rolePresent(TheAdmin) = PrivTypes.Guard) then
             (AdminToken.isGood and
                AdminToken.authCertValid and
                AdminToken.TheAuthCertRole = PrivTypes.Guard)) and

         (if (Admin.IsDoingOp(TheAdmin) and then
                Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock)
          then
             (Admin.rolePresent(TheAdmin) = PrivTypes.Guard)) and

         (if (Admin.rolePresent(TheAdmin) = PrivTypes.Guard) then
             ((Admin.IsDoingOp(TheAdmin) and then
                 Admin.TheCurrentOp(TheAdmin) = Admin.OverrideLock) or
                not Admin.IsDoingOp(TheAdmin))) and

         (if (not Admin.IsPresent(TheAdmin)) then
            (not Admin.IsDoingOp(TheAdmin))) and

         (if (Admin.IsDoingOp(TheAdmin) and then
                Admin.TheCurrentOp(TheAdmin) = Admin.ShutdownOp)
          then
             Enclave.statusIsWaitingStartAdminOp) and

         (if (Enclave.statusIsGotAdminToken or
                Enclave.statusIsWaitingRemoveAdminTokenFail)
          then
             not Admin.IsPresent(TheAdmin)) and

         (if (Enclave.statusIsWaitingStartAdminOp or
                Enclave.statusIsWaitingFinishAdminOp)
          then
            (Admin.IsDoingOp(TheAdmin) and
               Admin.IsPresent(TheAdmin) and
               Admin.rolePresent(TheAdmin) =
               Admin.rolePresent(TheAdmin'Old))) and

         (if Enclave.statusIsEnclaveQuiescent then
             (not Admin.IsDoingOp(TheAdmin))) and

         (if Enclave.statusIsShutdown then
             (not Admin.IsDoingOp(TheAdmin) and
                Admin.rolePresent(TheAdmin) = PrivTypes.UserOnly)) and

         (if Enclave.EnrolmentIsInProgress then
             (not Admin.IsPresent(TheAdmin) and
                not Admin.IsDoingOp(TheAdmin)))
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
        with Global  => (Input  => (Clock.Now,
                                    ConfigData.State,
                                    Enclave.State,
                                    TheAdmin,
                                    UserEntry.State),
                         In_Out => (AuditLog.FileState,
                                    AuditLog.State,
                                    Screen.State)),
             Depends => ((AuditLog.FileState,
                          AuditLog.State) => (AuditLog.FileState,
                                              AuditLog.State,
                                              Clock.Now,
                                              ConfigData.State,
                                              Enclave.State,
                                              Screen.State,
                                              TheAdmin,
                                              UserEntry.State),

                         Screen.State =>+ (Enclave.State,
                                           TheAdmin,
                                           UserEntry.State))
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

      elsif Enclave.AdminMustLogout(TheAdmin => TheAdmin) then
         Enclave.AdminLogout(TheAdmin => TheAdmin);
         ResetScreenMessage;

      elsif UserEntry.CurrentActivityPossible then
         UserEntry.Progress(TheStats => TheStats);
         ResetScreenMessage;

      elsif Enclave.CurrentAdminActivityPossible then
         Enclave.ProgressAdminActivity(TheAdmin => TheAdmin);

      elsif UserEntry.CanStart then
         UserEntry.StartEntry;
         ResetScreenMessage;

      else
         Enclave.StartAdminActivity(TheAdmin => TheAdmin);
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
     with Global  => (Input  => (AdminToken.Input,
                                 Bio.Input,
                                 Clock.Now,
                                 Door.Input,
                                 Floppy.Input,
                                 Keyboard.Inputs,
                                 UserToken.Input),
                      Output => (Clock.CurrentTime,
                                 SystemFault),
                      In_Out => (AdminToken.State,
                                 AdminToken.Status,
                                 Alarm.Output,
                                 AuditLog.FileState,
                                 AuditLog.State,
                                 CertificateStore.FileState,
                                 CertificateStore.State,
                                 ConfigData.FileState,
                                 ConfigData.State,
                                 Display.Output,
                                 Display.State,
                                 Door.State,
                                 Enclave.State,
                                 Floppy.Output,
                                 Floppy.State,
                                 Floppy.WrittenState,
                                 KeyStore.State,
                                 KeyStore.Store,
                                 Latch.Output,
                                 Latch.State,
                                 Screen.Output,
                                 Screen.State,
                                 TheAdmin,
                                 TheStats,
                                 UserEntry.State,
                                 UserToken.Output,
                                 UserToken.State,
                                 UserToken.Status)),
          Depends => (AdminToken.State =>+ (AdminToken.Input,
                                            AdminToken.Status,
                                            Clock.Now,
                                            Door.Input,
                                            Door.State,
                                            Enclave.State,
                                            KeyStore.State,
                                            KeyStore.Store,
                                            Latch.State,
                                            TheAdmin,
                                            UserEntry.State,
                                            UserToken.Input,
                                            UserToken.State,
                                            UserToken.Status),

                      AdminToken.Status =>+ (AdminToken.Input,
                                             AdminToken.State,
                                             Clock.Now,
                                             Door.Input,
                                             Enclave.State,
                                             Latch.State,
                                             TheAdmin,
                                             UserEntry.State,
                                             UserToken.Input,
                                             UserToken.State,
                                             UserToken.Status),

                      (Alarm.Output,
                       AuditLog.FileState,
                       AuditLog.State,
                       Screen.Output,
                       Screen.State) =>+ (AdminToken.Input,
                                          AdminToken.State,
                                          AdminToken.Status,
                                          AuditLog.FileState,
                                          AuditLog.State,
                                          Bio.Input,
                                          CertificateStore.FileState,
                                          CertificateStore.State,
                                          Clock.Now,
                                          ConfigData.FileState,
                                          ConfigData.State,
                                          Display.State,
                                          Door.Input,
                                          Door.State,
                                          Enclave.State,
                                          Floppy.Input,
                                          Floppy.State,
                                          Floppy.WrittenState,
                                          Keyboard.Inputs,
                                          KeyStore.State,
                                          KeyStore.Store,
                                          Latch.State,
                                          Screen.State,
                                          TheAdmin,
                                          TheStats,
                                          UserEntry.State,
                                          UserToken.Input,
                                          UserToken.State,
                                          UserToken.Status),

                      (CertificateStore.FileState,
                       CertificateStore.State,
                       UserToken.Status) =>+ (AdminToken.Input,
                                              AdminToken.State,
                                              AdminToken.Status,
                                              CertificateStore.State,
                                              Clock.Now,
                                              ConfigData.State,
                                              Door.Input,
                                              Enclave.State,
                                              KeyStore.State,
                                              KeyStore.Store,
                                              Latch.State,
                                              TheAdmin,
                                              UserEntry.State,
                                              UserToken.Input,
                                              UserToken.State,
                                              UserToken.Status),

                      Clock.CurrentTime => Clock.Now,

                      (ConfigData.FileState,
                       ConfigData.State) =>+ (AdminToken.Input,
                                              AdminToken.State,
                                              AdminToken.Status,
                                              Clock.Now,
                                              Door.Input,
                                              Enclave.State,
                                              Floppy.State,
                                              Latch.State,
                                              TheAdmin,
                                              UserEntry.State,
                                              UserToken.Input,
                                              UserToken.State,
                                              UserToken.Status),

                      (Display.Output,
                       Display.State) =>+ (AdminToken.Input,
                                           AdminToken.State,
                                           AdminToken.Status,
                                           Bio.Input,
                                           CertificateStore.State,
                                           Clock.Now,
                                           ConfigData.State,
                                           Display.State,
                                           Door.Input,
                                           Door.State,
                                           Enclave.State,
                                           Floppy.State,
                                           KeyStore.State,
                                           KeyStore.Store,
                                           Latch.State,
                                           TheAdmin,
                                           UserEntry.State,
                                           UserToken.Input,
                                           UserToken.State,
                                           UserToken.Status),

                      (Door.State,
                       Latch.Output,
                       Latch.State) =>+ (AdminToken.Input,
                                         AdminToken.State,
                                         AdminToken.Status,
                                         Clock.Now,
                                         ConfigData.State,
                                         Door.Input,
                                         Door.State,
                                         Enclave.State,
                                         Latch.State,
                                         TheAdmin,
                                         UserEntry.State,
                                         UserToken.Input,
                                         UserToken.State,
                                         UserToken.Status),

                      SystemFault => (AdminToken.Input,
                                      AdminToken.State,
                                      AdminToken.Status,
                                      Clock.Now,
                                      ConfigData.State,
                                      Door.Input,
                                      Door.State,
                                      Enclave.State,
                                      Latch.State,
                                      TheAdmin,
                                      UserEntry.State,
                                      UserToken.Input,
                                      UserToken.State,
                                      UserToken.Status),

                      Enclave.State =>+ (AdminToken.Input,
                                         AdminToken.State,
                                         AdminToken.Status,
                                         Clock.Now,
                                         Door.Input,
                                         Door.State,
                                         Floppy.State,
                                         Keyboard.Inputs,
                                         KeyStore.State,
                                         KeyStore.Store,
                                         Latch.State,
                                         TheAdmin,
                                         UserEntry.State,
                                         UserToken.Input,
                                         UserToken.State,
                                         UserToken.Status),

                      Floppy.Output =>+ (AdminToken.Input,
                                         AdminToken.State,
                                         AdminToken.Status,
                                         AuditLog.FileState,
                                         AuditLog.State,
                                         Clock.Now,
                                         ConfigData.State,
                                         Display.State,
                                         Door.Input,
                                         Door.State,
                                         Enclave.State,
                                         Floppy.State,
                                         Latch.State,
                                         TheAdmin,
                                         UserEntry.State,
                                         UserToken.Input,
                                         UserToken.State,
                                         UserToken.Status),

                      Floppy.State =>+ (AdminToken.Input,
                                        AdminToken.State,
                                        AdminToken.Status,
                                        Clock.Now,
                                        Door.Input,
                                        Enclave.State,
                                        Floppy.Input,
                                        Latch.State,
                                        TheAdmin,
                                        UserEntry.State,
                                        UserToken.Input,
                                        UserToken.State,
                                        UserToken.Status),

                      Floppy.WrittenState =>+ (AdminToken.Input,
                                               AdminToken.State,
                                               AdminToken.Status,
                                               AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Display.State,
                                               Door.Input,
                                               Door.State,
                                               Enclave.State,
                                               Floppy.State,
                                               Latch.State,
                                               TheAdmin,
                                               UserEntry.State,
                                               UserToken.Input,
                                               UserToken.State,
                                               UserToken.Status),

                      (KeyStore.State,
                       KeyStore.Store) =>+ (Clock.Now,
                                            Door.Input,
                                            Enclave.State,
                                            Floppy.State,
                                            KeyStore.Store,
                                            Latch.State),

                      TheAdmin =>+ (AdminToken.Input,
                                    AdminToken.State,
                                    AdminToken.Status,
                                    Clock.Now,
                                    Door.Input,
                                    Door.State,
                                    Enclave.State,
                                    Keyboard.Inputs,
                                    KeyStore.State,
                                    KeyStore.Store,
                                    Latch.State,
                                    UserEntry.State,
                                    UserToken.Input,
                                    UserToken.State,
                                    UserToken.Status),

                      TheStats =>+ (AdminToken.Input,
                                    AdminToken.State,
                                    AdminToken.Status,
                                    Bio.Input,
                                    Clock.Now,
                                    ConfigData.State,
                                    Door.Input,
                                    Enclave.State,
                                    Latch.State,
                                    TheAdmin,
                                    UserEntry.State,
                                    UserToken.Input,
                                    UserToken.State,
                                    UserToken.Status),

                      UserEntry.State =>+ (AdminToken.Input,
                                           AdminToken.State,
                                           AdminToken.Status,
                                           Bio.Input,
                                           Clock.Now,
                                           ConfigData.State,
                                           Door.Input,
                                           Enclave.State,
                                           KeyStore.State,
                                           KeyStore.Store,
                                           Latch.State,
                                           TheAdmin,
                                           UserToken.Input,
                                           UserToken.State,
                                           UserToken.Status),

                      UserToken.Output =>+ (AdminToken.Input,
                                            AdminToken.State,
                                            AdminToken.Status,
                                            CertificateStore.State,
                                            Clock.Now, ConfigData.State,
                                            Door.Input,
                                            Enclave.State,
                                            KeyStore.State,
                                            KeyStore.Store,
                                            Latch.State,
                                            TheAdmin,
                                            UserEntry.State,
                                            UserToken.Input,
                                            UserToken.State,
                                            UserToken.Status),

                      UserToken.State =>+ (AdminToken.Input,
                                           AdminToken.State,
                                           AdminToken.Status,
                                           CertificateStore.State,
                                           Clock.Now,
                                           ConfigData.State,
                                           Door.Input,
                                           Door.State,
                                           Enclave.State,
                                           KeyStore.State,
                                           KeyStore.Store,
                                           Latch.State,
                                           TheAdmin,
                                           UserEntry.State,
                                           UserToken.Input,
                                           UserToken.Status)),

          Pre     =>
            (not Enclave.EnrolmentIsInProgress =
                KeyStore.PrivateKeyPresent) and

            (Latch.IsLocked = Latch.LatchIsLocked) and

            (if Admin.RolePresent (TheAdmin) = PrivTypes.Guard then
                (AdminToken.isGood and
                   AdminToken.authCertValid and
                   AdminToken.TheAuthCertRole = PrivTypes.Guard)) and

            (if (Admin.IsDoingOp (TheAdmin) and then
                   Admin.TheCurrentOp (TheAdmin) = Admin.OverrideLock)
             then
                Admin.RolePresent (TheAdmin) = PrivTypes.Guard) and

            (if Admin.RolePresent (TheAdmin) = PrivTypes.Guard then
                ((Admin.IsDoingOp (TheAdmin) and then
                    Admin.TheCurrentOp (TheAdmin) = Admin.OverrideLock) or
                   not Admin.IsDoingOp (TheAdmin))) and

            (if not Admin.IsPresent (TheAdmin) then
                not Admin.IsDoingOp (TheAdmin)) and

            (if (Admin.IsDoingOp (TheAdmin) and then
                   Admin.TheCurrentOp (TheAdmin) = Admin.ShutdownOp)
             then
                Enclave.statusIsWaitingStartAdminOp) and

            (if (Enclave.statusIsGotAdminToken or
                   Enclave.StatusIsWaitingRemoveAdminTokenFail)
             then
                not Admin.IsPresent (TheAdmin)) and

            (if (Enclave.statusIsWaitingStartAdminOp or
                   Enclave.statusIsWaitingFinishAdminOp)
             then
                (Admin.IsPresent (TheAdmin) and
                   Admin.IsDoingOp (TheAdmin))) and

            (if Enclave.statusIsEnclaveQuiescent then
                not Admin.IsDoingOp (TheAdmin)) and

            (if Enclave.statusIsShutdown then
                (not Admin.IsDoingOp (TheAdmin) and
                   Admin.RolePresent (TheAdmin) = PrivTypes.UserOnly)) and

            (if Enclave.EnrolmentIsInProgress then
                (not Admin.IsPresent (TheAdmin) and
                   not Admin.IsDoingOp (TheAdmin))),

          Post    =>
            (not Enclave.EnrolmentIsInProgress =
               KeyStore.PrivateKeyPresent) and

            (Latch.IsLocked = Latch.LatchIsLocked
               or SystemFault) and

            -------------------------------------------------------
            -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3         --
            --===================================================--
            -- After each call to MainLoopBody, either the       --
            -- security property holds, or a critical system     --
            -- fault has occurred, in which case the TIS will be --
            -- shutdown                                          --
            -------------------------------------------------------
            (if (Latch.IsLocked and
                   Door.TheCurrentDoor = Door.Open and
                   Clock.GreaterThanOrEqual (Clock.TheCurrentTime,
                                             Door.Alarm_Timeout))
             then
                (Alarm.isAlarming or SystemFault)) and

            (not (Latch.LatchIsLocked'Old and
                    not Latch.LatchIsLocked and
                    not Latch.IsLocked and
                    Latch.IsLocked'Old = Latch.LatchIsLocked'Old)
             or
               ((Latch.IsLocked'Old or not Latch.IsLocked) or
                  (AdminToken.isGood and
                     AdminToken.authCertValid and
                     AdminToken.TheAuthCertRole = PrivTypes.Guard) or
                  SystemFault)) and

            (if Admin.RolePresent (TheAdmin) = PrivTypes.Guard then
                (AdminToken.isGood and
                   AdminToken.authCertValid and
                   AdminToken.TheAuthCertRole = PrivTypes.Guard)) and

            (if (Admin.IsDoingOp (TheAdmin) and then
                   Admin.TheCurrentOp (TheAdmin) = Admin.OverrideLock)
             then
                Admin.RolePresent (TheAdmin) = PrivTypes.Guard) and

            (if Admin.RolePresent (TheAdmin) = PrivTypes.Guard then
                ((Admin.IsDoingOp (TheAdmin) and then
                    Admin.TheCurrentOp (TheAdmin) = Admin.OverrideLock) or
                   not Admin.IsDoingOp (TheAdmin))) and

            (if not Admin.IsPresent (TheAdmin) then
                not Admin.IsDoingOp (TheAdmin)) and

            (if (Admin.IsDoingOp (TheAdmin) and then
                   Admin.TheCurrentOp (TheAdmin) = Admin.ShutdownOp)
             then
                Enclave.statusIsWaitingStartAdminOp) and

            (if (Enclave.statusIsGotAdminToken or
                   Enclave.statusIsWaitingRemoveAdminTokenFail)
             then
                not Admin.IsPresent (TheAdmin)) and

            (if (Enclave.statusIsWaitingStartAdminOp or
                   Enclave.statusIsWaitingFinishAdminOp)
             then
                (Admin.IsDoingOp (TheAdmin) and
                   Admin.IsPresent (TheAdmin) and
                   Admin.RolePresent (TheAdmin) =
                     Admin.RolePresent (TheAdmin'Old))) and

            (if Enclave.statusIsEnclaveQuiescent then
                not Admin.IsDoingOp (TheAdmin)) and

            (if Enclave.statusIsShutdown then
                (not Admin.IsDoingOp (TheAdmin) and
                   Admin.RolePresent (TheAdmin) = PrivTypes.UserOnly)) and

            (if Enclave.EnrolmentIsInProgress then
                (not Admin.IsPresent (TheAdmin) and
                   not Admin.IsDoingOp (TheAdmin)))
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
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State,
                                 TheStats),
                      Output => (Alarm.Output,
                                 Door.State,
                                 Latch.Output,
                                 Latch.State,
                                 Screen.Output,
                                 TheAdmin),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 Display.Output,
                                 Display.State,
                                 Screen.State)),
          Depends => ((Alarm.Output,
                       AuditLog.FileState,
                       AuditLog.State,
                       Screen.Output,
                       Screen.State) => (AuditLog.FileState,
                                         AuditLog.State,
                                         Clock.Now,
                                         ConfigData.State,
                                         Display.State,
                                         Screen.State,
                                         TheStats),

                      (Display.Output,
                       Display.State) =>+ Display.State,

                      (Door.State,
                       Latch.Output,
                       Latch.State,
                       TheAdmin) => null)
   is
      UnusedFault : Boolean;
   begin
      Door.Failure;
      Admin.Logout(TheAdmin => TheAdmin);

      pragma Warnings (Off);
      Updates.Activity(SystemFault => UnusedFault,
                       TheStats    => TheStats,
                       TheAdmin    => TheAdmin);
      pragma Warnings (On);
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
     with Global  => (Input  => (Clock.CurrentTime,
                                 Clock.Now,
                                 ConfigData.State,
                                 TheStats),
                      Output => (Alarm.Output,
                                 Latch.Output,
                                 Screen.Output,
                                 TheAdmin),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 Display.Output,
                                 Display.State,
                                 Door.State,
                                 Latch.State,
                                 Screen.State)),
          Depends => ((Alarm.Output,
                       AuditLog.FileState,
                       AuditLog.State,
                       Screen.Output,
                       Screen.State) => (AuditLog.FileState,
                                         AuditLog.State,
                                         Clock.CurrentTime,
                                         Clock.Now,
                                         ConfigData.State,
                                         Display.State,
                                         Door.State,
                                         Latch.State,
                                         Screen.State,
                                         TheStats),

                      (Display.Output,
                       Display.State) =>+ Display.State,

                      (Door.State,
                       Latch.State) =>+ (Clock.CurrentTime,
                                         Latch.State),

                      Latch.Output => (Clock.CurrentTime,
                                       Latch.State),

                      TheAdmin => null)
   is
      UnusedFault : Boolean;
   begin
      Door.LockDoor;
      Admin.Logout(TheAdmin => TheAdmin);

      pragma Warnings (Off);
      Updates.Activity(SystemFault => UnusedFault,
                       TheStats    => TheStats,
                       TheAdmin    => TheAdmin);
      pragma Warnings (On);
   end ShutdownAuditLogFailure;

begin

   Init;

   -- In order to show that (the admin part of) security
   -- property 1 holds, the changes to Latch.State and
   -- Latch.Output need to be recorded.
   -- Two proof functions prf_preLatchState and
   -- prf_preLatchOutput have been introduced to model
   -- the values of Latch.State and Latch.Output at the
   -- start of the main loop. These are then used in
   -- assertions further down the loop.
   -- VC1 and VC2 both have conclusions C1 and C2 that show
   -- this.
   --
   -- VC1 (which represents the path from the start to the
   -- first assertion) also has a conclusion C3 which is not
   -- actually true. Latch.Output is not defined until the first
   -- call to Update, which is within MainLoopBody. This is
   -- acceptable though, since the Latch will not be updated on the
   -- first iteration of the loop. For the latch to be altered,
   -- Either a guard is present, or a user entry is in progress.
   -- For these conditions to be true, at least one iteration must
   -- have taken place.
   pragma Assume (Latch.IsLocked = Latch.LatchIsLocked);

   loop

      pragma Loop_Invariant
        (((not Enclave.EnrolmentIsInProgress) = KeyStore.PrivateKeyPresent) and

         --  Latch.LatchIsLocked = Latch.LatchIsLocked'Loop_Entry and
         --  Latch.LatchIsLocked = Latch.LatchIsLocked'Loop_Entry and
         Latch.IsLocked = Latch.LatchIsLocked and

         (if Admin.RolePresent (TheAdmin) = PrivTypes.Guard then
             (AdminToken.IsGood and
                AdminToken.AuthCertValid and
                AdminToken.TheAuthCertRole = PrivTypes.Guard)) and

         (if (Admin.IsDoingOp (TheAdmin) and then
                Admin.TheCurrentOp (TheAdmin) = Admin.OverrideLock)
          then
             Admin.RolePresent (TheAdmin) = PrivTypes.Guard) and

         (if Admin.RolePresent (TheAdmin) = PrivTypes.Guard then
             ((Admin.IsDoingOp (TheAdmin) and then
                 Admin.TheCurrentOp (TheAdmin) = Admin.OverrideLock) or
                not Admin.IsDoingOp (TheAdmin))) and

         (if not Admin.IsPresent (TheAdmin) then
             not Admin.IsDoingOp (TheAdmin)) and

         (if (Admin.IsDoingOp (TheAdmin) and then
                Admin.TheCurrentOp (TheAdmin) = Admin.ShutdownOp)
          then
             Enclave.statusIsWaitingStartAdminOp) and

         (if (Enclave.statusIsGotAdminToken or
                Enclave.statusIsWaitingRemoveAdminTokenFail)
          then
             not Admin.IsPresent (TheAdmin)) and

         (if (Enclave.statusIsWaitingStartAdminOp or
             Enclave.statusIsWaitingFinishAdminOp)
          then
             (Admin.IsPresent (TheAdmin) and Admin.IsDoingOp (TheAdmin))) and

         (if Enclave.statusIsEnclaveQuiescent then
             not Admin.IsDoingOp (TheAdmin)) and

         (if Enclave.statusIsShutdown then
             (not Admin.IsDoingOp (TheAdmin) and
                Admin.RolePresent (TheAdmin) = PrivTypes.UserOnly)) and

         (if Enclave.EnrolmentIsInProgress then
             (not Admin.IsPresent (TheAdmin) and
                not Admin.IsDoingOp (TheAdmin))));

      MainLoopBody;

      ShutdownCompleted := Enclave.HasShutdown;

      exit when ShutdownCompleted;

      pragma Assert_And_Cut
        (not ShutdownCompleted and
         ((not Enclave.EnrolmentIsInProgress) = KeyStore.PrivateKeyPresent) and

         -------------------------------------------------------
         -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3         --
         --===================================================--
         -- After each cycle of the TIS main loop, either the --
         -- security property holds, or a critical system     --
         -- fault has occurred, in which case the TIS will be --
         -- shutdown                                          --
         -------------------------------------------------------

         (if (Latch.IsLocked and
                Door.TheCurrentDoor = Door.Open and
                Clock.GreaterThanOrEqual (Clock.TheCurrentTime,
                                          Door.Alarm_Timeout))
          then
             (Alarm.IsAlarming or SystemFault)) and

         --   ((if (Latch.prf_isLocked (prf_preLatchOutput) and
         --           not Latch.prf_isLocked (Latch.Output) and
         --           Latch.IsLocked (prf_preLatchState) =
         --             Latch.prf_isLocked (prf_preLatchOutput))
         --     then
         --        (UserEntry.prf_UserEntryUnlockDoor or
         --           (AdminToken.prf_isGood (AdminToken.State) and
         --              AdminToken.prf_authCertValid (AdminToken.State) and
         --              AdminToken.TheAuthCertRole (AdminToken.State) =
         --                PrivTypes.Guard)))
         --  or SystemFault) and

         (Latch.IsLocked = Latch.LatchIsLocked or SystemFault) and

         (if Admin.RolePresent (TheAdmin) = PrivTypes.Guard then
             (AdminToken.IsGood and
                AdminToken.AuthCertValid and
                AdminToken.TheAuthCertRole = PrivTypes.Guard)) and

         (if (Admin.IsDoingOp (TheAdmin) and then
                Admin.TheCurrentOp (TheAdmin) = Admin.OverrideLock)
          then
            Admin.RolePresent (TheAdmin) = PrivTypes.Guard) and

         (if Admin.RolePresent (TheAdmin) = PrivTypes.Guard then
             ((Admin.IsDoingOp (TheAdmin) and then
                 Admin.TheCurrentOp (TheAdmin) = Admin.OverrideLock) or
                not Admin.IsDoingOp (TheAdmin))) and

         (if not Admin.IsPresent (TheAdmin) then
             not Admin.IsDoingOp (TheAdmin)) and

         (if (Admin.IsDoingOp (TheAdmin) and then
                Admin.TheCurrentOp (TheAdmin) = Admin.ShutdownOp)
          then
             Enclave.statusIsWaitingStartAdminOp) and

         (if (Enclave.statusIsGotAdminToken or
                Enclave.statusIsWaitingRemoveAdminTokenFail)
          then
             not Admin.IsPresent (TheAdmin)) and

         (if (Enclave.statusIsWaitingStartAdminOp or
                Enclave.statusIsWaitingFinishAdminOp)
          then
             (Admin.IsDoingOp (TheAdmin) and
                Admin.IsPresent (TheAdmin))) and

         (if Enclave.statusIsEnclaveQuiescent then
             (not Admin.IsDoingOp (TheAdmin))) and

         (if Enclave.statusIsShutdown then
             (not Admin.IsDoingOp (TheAdmin) and
                Admin.RolePresent (TheAdmin) = PrivTypes.UserOnly)) and

         (if Enclave.EnrolmentIsInProgress then
             (not Admin.IsPresent (TheAdmin) and
                not Admin.IsDoingOp (TheAdmin))));

      if SystemFault then
         pragma Warnings (Off);
         ShutdownDoorLatchFailure;
         pragma Warnings (On);
         exit;
      end if;

      if AuditLog.SystemFaultOccurred then
         pragma Warnings (Off);
         ShutdownAuditLogFailure;
         pragma Warnings (On);
         exit;
      end if;

      pragma Assert_And_Cut
        (not ShutdownCompleted and not SystemFault and

         ((not Enclave.EnrolmentIsInProgress) = KeyStore.PrivateKeyPresent) and

         -------------------------------------------------------
         -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3         --
         --===================================================--
         -- After each cycle of the TIS main loop, either the --
         -- security property holds, or a critical system     --
         -- fault has occurred, in which case the TIS will be --
         -- shutdown                                          --
         -------------------------------------------------------

         (if (Latch.IsLocked and
                Door.TheCurrentDoor = Door.Open and
                Clock.GreaterThanOrEqual (Clock.TheCurrentTime,
                                          Door.Alarm_Timeout))
          then
             (Alarm.isAlarming or SystemFault)) and

         --  (if (Latch.prf_isLocked (prf_preLatchOutput) and
         --         not Latch.prf_isLocked (Latch.Output) and
         --         Latch.IsLocked (prf_preLatchState) =
         --           Latch.prf_isLocked (prf_preLatchOutput))
         --   then
         --      (UserEntry.prf_UserEntryUnlockDoor or
         --         (AdminToken.prf_isGood (AdminToken.State) and
         --            AdminToken.prf_authCertValid (AdminToken.State) and
         --            AdminToken.TheAuthCertRole (AdminToken.State) =
         --              PrivTypes.Guard))) and

         (Latch.IsLocked = Latch.LatchIsLocked or SystemFault) and

         (if Admin.RolePresent (TheAdmin) = PrivTypes.Guard then
             (AdminToken.IsGood and
                AdminToken.AuthCertValid and
                AdminToken.TheAuthCertRole = PrivTypes.Guard)) and

         (if (Admin.IsDoingOp (TheAdmin) and then
                Admin.TheCurrentOp (TheAdmin) = Admin.OverrideLock)
          then
             Admin.RolePresent (TheAdmin) = PrivTypes.Guard) and

         (if Admin.RolePresent (TheAdmin) = PrivTypes.Guard then
             ((Admin.IsDoingOp (TheAdmin) and then
                 Admin.TheCurrentOp (TheAdmin) = Admin.OverrideLock) or
                not Admin.IsDoingOp (TheAdmin))) and

         (if not Admin.IsPresent (TheAdmin) then
             not Admin.IsDoingOp (TheAdmin)) and

         (if (Admin.IsDoingOp (TheAdmin) and then
                Admin.TheCurrentOp (TheAdmin) = Admin.ShutdownOp)
          then
             Enclave.statusIsWaitingStartAdminOp) and

         (if (Enclave.statusIsGotAdminToken or
                Enclave.statusIsWaitingRemoveAdminTokenFail)
          then
             not Admin.IsPresent (TheAdmin)) and

         (if (Enclave.statusIsWaitingStartAdminOp or
                Enclave.statusIsWaitingFinishAdminOp)
          then
             (Admin.IsDoingOp (TheAdmin) and
                Admin.IsPresent (TheAdmin))) and

         (if Enclave.statusIsEnclaveQuiescent then
             (not Admin.IsDoingOp (TheAdmin))) and

         (if Enclave.statusIsShutdown then
             (not Admin.IsDoingOp (TheAdmin) and
                Admin.RolePresent (TheAdmin) = PrivTypes.UserOnly)) and

         (if Enclave.EnrolmentIsInProgress then
             (not Admin.IsPresent (TheAdmin) and
                not Admin.IsDoingOp (TheAdmin))));

   end loop;

   Keyboard.Finalise;

end TISMain;
