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
-- UserEntry
--
-- Implementation Notes:
--    Implements UserEntry
--
------------------------------------------------------------------

with BasicTypes;
use type BasicTypes.PresenceT;

with IandATypes;
use type IandATypes.MatchResultT;
use type IandATypes.FarT;

with Bio;
with AuditLog;
with AuditTypes;
with UserToken;
with Display;
with Door;
with Latch;
with Clock;
with ConfigData;
with CertificateStore;


package body UserEntry
--# own State is Status,
--#              FingerTimeout,
--#              TokenRemovalTimeout;
is


   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   type StatusT is (Quiescent,
                    GotUserToken,
                    WaitingFinger,
                    GotFinger,
                    WaitingUpdateToken,
                    WaitingEntry,
                    WaitingRemoveTokenSuccess,
                    WaitingRemoveTokenFail);

   ------------------------------------------------------------------
   -- State
   --
   ------------------------------------------------------------------
   Status : StatusT := Quiescent;

   FingerTimeout       : Clock.TimeT := Clock.ZeroTime;
   TokenRemovalTimeout : Clock.TimeT := Clock.ZeroTime;

   ------------------------------------------------------------------
   -- Local Operations
   ------------------------------------------------------------------

   ------------------------------------------------------------------
   -- UserHasDeparted
   --
   -- Description:
   --    Determines whether the User has just departed.
   --
   -- Implementation Notes:
   --    None.
   --
   -- Traceunit : C.UserEntry.UserHasDeparted
   -- Traceto : FD.UserEntry.UserHasDeparted
   ------------------------------------------------------------------
   function UserHasDeparted return Boolean
   --# global Status,
   --#        UserToken.State;
   is
   begin
      return Status > Quiescent and not UserToken.IsPresent;
   end UserHasDeparted;

   ------------------------------------------------------------------
   -- UserTokenTorn
   --
   -- Description:
   --    Handles a user token tear.
   --
   -- Implementation Notes:
   --    None.
   --
   -- Traceunit : C.UserEntry.UserTokenTorn
   -- Traceto : FD.UserEntry.UserTokenTorn
   ------------------------------------------------------------------
   procedure UserTokenTorn(TheStats : in out Stats.T)
   --# global in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in out UserToken.State;
   --#        in out Display.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#           out Status;
   --# derives UserToken.State,
   --#         Display.State,
   --#         TheStats           from * &
   --#         AuditLog.State,
   --#         AuditLog.FileState from UserToken.State,
   --#                                 Display.State,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 ConfigData.State,
   --#                                 Clock.Now &
   --#         Status             from ;
   is

   begin

      AuditLog.AddElementToLog
        ( ElementID   => AuditTypes.UserTokenRemoved,
          Severity    => AuditTypes.Warning,
          User        => UserToken.ExtractUser,
          Description => AuditTypes.NoDescription
          );

      Display.SetValue (Msg => Display.Welcome);
      Status := Quiescent;

      Stats.AddFailedEntry (TheStats => TheStats);
      UserToken.Clear;

   end UserTokenTorn;

   ------------------------------------------------------------------
   -- ValidateUserToken
   --
   -- Description:
   --    Reads and validates the user token.
   --    Performs all actions when Status = GotUserToken
   --
   -- Implementation Notes:
   --    Since it is expensive to read all the certificates from the
   --    token they are only read if required. This means that the
   --    reading of the certificates from the token is postponed until
   --    this operation.
   --
   -- Traceunit : C.UserEntry.ValidateUserToken
   -- Traceto : FD.UserEntry.TISReadUserToken
   -- Traceto : FD.UserEntry.BioCheckNotRequired
   -- Traceto : FD.UserEntry.BioCheckRequired
   -- Traceto : FD.UserEntry.ValidateUserEntryFail
   -- Traceto : FD.UserEntry.UserTokenTorn
   ------------------------------------------------------------------
   procedure ValidateUserToken(TheStats : in out Stats.T)
   --# global in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in     UserToken.Input;
   --#        in     Clock.CurrentTime;
   --#        in     KeyStore.Store;
   --#        in     KeyStore.State;
   --#        in     Bio.Input;
   --#        in out UserToken.State;
   --#        in out Display.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#        in out UserToken.Status;
   --#        in out FingerTimeout;
   --#           out Status;
   --# derives Status,
   --#         UserToken.State,
   --#         UserToken.Status   from UserToken.State,
   --#                                 UserToken.Status,
   --#                                 UserToken.Input,
   --#                                 Clock.CurrentTime,
   --#                                 KeyStore.Store,
   --#                                 KeyStore.State &
   --#         AuditLog.State,
   --#         AuditLog.FileState from UserToken.State,
   --#                                 Display.State,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 ConfigData.State,
   --#                                 Clock.Now,
   --#                                 UserToken.Status,
   --#                                 UserToken.Input,
   --#                                 Clock.CurrentTime,
   --#                                 KeyStore.Store,
   --#                                 KeyStore.State &
   --#         Display.State      from *,
   --#                                 UserToken.State,
   --#                                 UserToken.Status,
   --#                                 UserToken.Input,
   --#                                 Clock.CurrentTime,
   --#                                 KeyStore.Store,
   --#                                 KeyStore.State &
   --#         TheStats           from *,
   --#                                 UserToken.State &
   --#         FingerTimeout      from *,
   --#                                 UserToken.State,
   --#                                 ConfigData.State,
   --#                                 UserToken.Status,
   --#                                 UserToken.Input,
   --#                                 Clock.CurrentTime,
   --#                                 KeyStore.Store,
   --#                                 KeyStore.State &
   --#         null               from Bio.Input;
   is

     AuthCertOK : Boolean;
     TokenOK : Boolean;

     Description : AuditTypes.DescriptionT;
   begin

      if not UserToken.IsPresent then

         UserTokenTorn(TheStats => TheStats);

      else

         UserToken.ReadAndCheckAuthCert (AuthCertOK => AuthCertOK);

         if AuthCertOK then

            -- GetPresentUserTokenC postponed actions

            AuditLog.AddElementToLog
              ( ElementID   => AuditTypes.UserTokenPresent,
                Severity    => AuditTypes.Information,
                User        => UserToken.ExtractUser,
                Description => AuditTypes.NoDescription
                );

            -- BioCheckNotRequiredC actions

            AuditLog.AddElementToLog
              ( ElementID   => AuditTypes.AuthCertValid,
                Severity    => AuditTypes.Information,
                User        => UserToken.ExtractUser,
                Description => AuditTypes.NoDescription
                );

            Display.SetValue (Msg => Display.Wait);
            Status := WaitingEntry;
         else

            UserToken.ReadAndCheck
              (Description => Description,
               TokenOK     => TokenOK);

            if TokenOK then

               -- GetPresentUserTokenC postponed actions

               AuditLog.AddElementToLog
                 ( ElementID   => AuditTypes.UserTokenPresent,
                   Severity    => AuditTypes.Information,
                   User        => UserToken.ExtractUser,
                   Description => AuditTypes.NoDescription
                   );

               -- BioCheckRequiredC actions

               AuditLog.AddElementToLog
                 ( ElementID   => AuditTypes.AuthCertInvalid,
                   Severity    => AuditTypes.Information,
                   User        => UserToken.ExtractUser,
                   Description => AuditTypes.NoDescription
                   );

               Display.SetValue (Msg => Display.InsertFinger);
               Status := WaitingFinger;

               FingerTimeout := Clock.AddDuration
                 ( TheTime     => Clock.TheCurrentTime,
                   TheDuration => ConfigData.TheFingerWaitDuration );

               -- Flush any stale BIO data.
               Bio.Flush;

            else
               -- GetPresentUserTokenC postponed actions

               AuditLog.AddElementToLog
                 ( ElementID   => AuditTypes.UserTokenPresent,
                   Severity    => AuditTypes.Information,
                   User        => UserToken.ExtractUser,
                   Description => AuditTypes.NoDescription
                   );


               -- ValidateUserTokenFailC actions

               AuditLog.AddElementToLog
                 ( ElementID   => AuditTypes.UserTokenInvalid,
                   Severity    => AuditTypes.Warning,
                   User        => UserToken.ExtractUser,
                   Description => Description
                   );

               Display.SetValue (Msg => Display.RemoveToken);
               Status := WaitingRemoveTokenFail;

            end if;
         end if;
      end if;
   end ValidateUserToken;

   ------------------------------------------------------------------
   -- ReadFinger
   --
   -- Description:
   --    Reads and fingerprint.
   --    Performs all actions when Status = WaitingFinger
   --
   -- Implementation Notes:
   --    None.
   --
   -- Traceunit : C.UserEntry.ReadFinger
   -- Traceto : FD.UserEntry.ReadFingerOK
   -- Traceto : FD.UserEntry.NoFinger
   -- Traceto : FD.UserEntry.FingerTimeout
   -- Traceto : FD.UserEntry.UserTokenTorn
   ------------------------------------------------------------------
   procedure ReadFinger(TheStats : in out Stats.T)
   --# global in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in     Clock.CurrentTime;
   --#        in     FingerTimeout;
   --#        in     Bio.Input;
   --#        in out Status;
   --#        in out UserToken.State;
   --#        in out Display.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --# derives Status,
   --#         Display.State      from *,
   --#                                 UserToken.State,
   --#                                 Clock.CurrentTime,
   --#                                 FingerTimeout,
   --#                                 Bio.Input &
   --#         UserToken.State,
   --#         TheStats           from *,
   --#                                 UserToken.State &
   --#         AuditLog.State,
   --#         AuditLog.FileState from UserToken.State,
   --#                                 Display.State,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 ConfigData.State,
   --#                                 Clock.Now,
   --#                                 Clock.CurrentTime,
   --#                                 FingerTimeout,
   --#                                 Bio.Input;
   --# pre Status = WaitingFinger;
   is

     FingerPresence : BasicTypes.PresenceT;
   begin

      if not UserToken.IsPresent then

         UserTokenTorn(TheStats => TheStats);

      else

         if Clock.GreaterThan(Clock.TheCurrentTime, FingerTimeout) then

            -- FingerTimeoutC actions

            AuditLog.AddElementToLog
              ( ElementID   => AuditTypes.FingerTimeout,
                Severity    => AuditTypes.Warning,
                User        => UserToken.ExtractUser,
                Description => AuditTypes.NoDescription
                );

            Display.SetValue (Msg => Display.RemoveToken);
            Status := WaitingRemoveTokenFail;

         else

            Bio.Poll(FingerPresent => FingerPresence);

            if FingerPresence = BasicTypes.Present then

               -- ReadFingerOKC actions

               AuditLog.AddElementToLog
                 ( ElementID   => AuditTypes.FingerDetected,
                   Severity    => AuditTypes.Information,
                   User        => UserToken.ExtractUser,
                   Description => AuditTypes.NoDescription
                   );

               Display.SetValue (Msg => Display.Wait);
               Status := GotFinger;


            else
               -- NoFingerC actions
               null;

            end if;

         end if;

      end if;
   end ReadFinger;



   ------------------------------------------------------------------
   -- ValidateFinger
   --
   -- Description:
   --    Validates and fingerprint.
   --    Performs all actions when Status = GotFinger
   --
   -- Implementation Notes:
   --    None.
   --
   -- Traceunit : C.UserEntry.ValidateFinger
   -- Traceto : FD.UserEntry.ValidateFingerOK
   -- Traceto : FD.UserEntry.ValidateFingerFail
   -- Traceto : FD.UserEntry.UserTokenTorn
   ------------------------------------------------------------------
   procedure ValidateFinger (TheStats : in out Stats.T)
   --# global in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in     Bio.Input;
   --#        in out UserToken.State;
   --#        in out Display.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#           out Status;
   --# derives Display.State,
   --#         TheStats           from *,
   --#                                 UserToken.State,
   --#                                 ConfigData.State,
   --#                                 Bio.Input &
   --#         AuditLog.State,
   --#         AuditLog.FileState from UserToken.State,
   --#                                 Display.State,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 ConfigData.State,
   --#                                 Clock.Now,
   --#                                 Bio.Input &
   --#         Status             from UserToken.State,
   --#                                 ConfigData.State,
   --#                                 Bio.Input &
   --#         UserToken.State    from *;
   is

      TheTemplate : IandATypes.TemplateT;
      MatchResult : IandATypes.MatchResultT;
      AchievedFAR : IandATypes.FarT;
      MaxFAR      : IandATypes.FarT;


   ------------------------------------------------------------------
   -- AchievedFarDescription
   --
   -- Description:
   --    Produces a description for the Audit log from the
   --    supplied FAR.
   --
   -- Implementation Notes:
   --    None
   ------------------------------------------------------------------
   function AchievedFARDescription return AuditTypes.DescriptionT
   --# global AchievedFAR;
   is
      Result : AuditTypes.DescriptionT := AuditTypes.NoDescription;

      ------------------------------------------------------------------
      -- SetResultString
      --
      -- Description:
      --    Sets the Result string allowing for overflow.
      --
      -- Implementation Notes:
      --    Hidden because of use of slices.
      ------------------------------------------------------------------
      procedure SetResultString
      --# global in     AchievedFAR;
      --#        in out Result;
      --# derives Result from *,
      --#                     AchievedFAR;
      is
         --# hide SetResultString;

         FullString : String := "Acheived FAR : "
           & IandATypes.FarT'Image(AchievedFAR) ;
      begin

         -- if the Full string is shorter then use it all otherwise
         -- truncate it.
         if FullString'Last <= AuditTypes.DescriptionI'Last then
            Result (1.. FullString'Last) := FullString;
         else
            Result := FullString (1 .. AuditTypes.DescriptionI'Last);
         end if;
      end SetResultString;


   --------------------------------------------------------------------
   -- begin AchievedFARDescription
   --------------------------------------------------------------------
   begin

      SetResultString;

      return Result;

   end AchievedFARDescription;

   --------------------------------------------------------------------
   -- begin ValidateFinger
   --------------------------------------------------------------------

   begin

      if not UserToken.IsPresent then

         UserTokenTorn(TheStats => TheStats);

      else

         TheTemplate := UserToken.GetIandATemplate;

         MaxFar := ConfigData.TheSystemMaxFar;
         if TheTemplate.RequiredMaxFar < MaxFar then
            MaxFar := TheTemplate.RequiredMaxFar;
         end if;

         Bio.Verify
           ( Template    => TheTemplate,
             MaxFar      => MaxFar,
             MatchResult => MatchResult,
             AchievedFAR => AchievedFAR );

         -- ValidateFingerOKC and ValidateFingerFailC common actions

         -- Flush any stale BIO data.
         Bio.Flush;

         if MatchResult = IandATypes.Match then

            -- ValidateFingerOKC actions

            AuditLog.AddElementToLog
              ( ElementID   => AuditTypes.FingerMatched,
                Severity    => AuditTypes.Information,
                User        => UserToken.ExtractUser,
                Description => AchievedFARDescription
                );

            Display.SetValue (Msg => Display.Wait);
            Status := WaitingUpdateToken;

            Stats.AddSuccessfulBio(TheStats => TheStats);

         else
            -- ValidateFingerFailC actions

            AuditLog.AddElementToLog
              ( ElementID   => AuditTypes.FingerNotMatched,
                Severity    => AuditTypes.Warning,
                User        => UserToken.ExtractUser,
                Description => AchievedFARDescription
                );

            Display.SetValue (Msg => Display.RemoveToken);
            Status := WaitingRemoveTokenFail;

            Stats.AddFailedBio(TheStats => TheStats);

         end if;

      end if;

   end ValidateFinger;


   ------------------------------------------------------------------
   -- UpdateToken
   --
   -- Description:
   --    Updates the user token if required.
   --    Performs all actions when Status = WaitingUpdateToken.
   --
   -- Implementation Notes:
   --    None.
   --
   -- Traceunit : C.UserEntry.UpdateToken
   -- Traceto : FD.UserEntry.UpdateUserTokenNotRequired
   -- Traceto : FD.UserEntry.WriteUserTokenOK
   -- Traceto : FD.UserEntry.WriteUserTokenFail
   -- Traceto : FD.UserEntry.UserTokenTorn
   ------------------------------------------------------------------
   procedure UpdateToken(TheStats : in out Stats.T)
   --# global in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in     Clock.CurrentTime;
   --#        in     KeyStore.Store;
   --#        in     KeyStore.State;
   --#        in out UserToken.State;
   --#        in out Display.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#        in out UserToken.Status;
   --#        in out CertificateStore.FileState;
   --#        in out CertificateStore.State;
   --#           out Status;
   --#           out UserToken.Output;
   --# derives Display.State,
   --#         UserToken.Status,
   --#         CertificateStore.FileState,
   --#         CertificateStore.State     from *,
   --#                                         UserToken.State,
   --#                                         ConfigData.State,
   --#                                         UserToken.Status,
   --#                                         Clock.CurrentTime,
   --#                                         KeyStore.Store,
   --#                                         KeyStore.State,
   --#                                         CertificateStore.State &
   --#         AuditLog.State,
   --#         AuditLog.FileState         from UserToken.State,
   --#                                         Display.State,
   --#                                         AuditLog.State,
   --#                                         AuditLog.FileState,
   --#                                         ConfigData.State,
   --#                                         Clock.Now,
   --#                                         UserToken.Status,
   --#                                         Clock.CurrentTime,
   --#                                         KeyStore.Store,
   --#                                         KeyStore.State,
   --#                                         CertificateStore.FileState,
   --#                                         CertificateStore.State &
   --#         Status                     from UserToken.State &
   --#         UserToken.State            from *,
   --#                                         ConfigData.State,
   --#                                         Clock.CurrentTime,
   --#                                         KeyStore.State,
   --#                                         CertificateStore.State &
   --#         TheStats                   from *,
   --#                                         UserToken.State &
   --#         UserToken.Output           from UserToken.State,
   --#                                         ConfigData.State,
   --#                                         UserToken.Status,
   --#                                         Clock.CurrentTime,
   --#                                         KeyStore.Store,
   --#                                         KeyStore.State,
   --#                                         CertificateStore.State;
   --# pre Keystore.PrivateKeyPresent(KeyStore.State);
   is

      UpdateOK : Boolean;
   begin

      if not UserToken.IsPresent then

         UserTokenTorn(TheStats => TheStats);

      else

         -- ConstructAuthCert actions

         UserToken.AddAuthCert(Success => UpdateOK);

         -- WriteUserTokenOKC / WriteUserTokenFailC common actions

         Status := WaitingEntry;


         if UpdateOK then
            -- only add the certificate to the token if we could build one
            UserToken.UpdateAuthCert(Success => UpdateOK);
         end if;

         if UpdateOK then

            -- WriteUserTokenOKC actions

            AuditLog.AddElementToLog
              ( ElementID   => AuditTypes.AuthCertWritten,
                Severity    => AuditTypes.Information,
                User        => UserToken.ExtractUser,
                Description => AuditTypes.NoDescription
                );

            Display.SetValue (Msg => Display.Wait);

            CertificateStore.UpdateStore;

         else

            -- WriteUserTokenFailC actions

            AuditLog.AddElementToLog
              ( ElementID   => AuditTypes.AuthCertWriteFailed,
                Severity    => AuditTypes.Warning,
                User        => UserToken.ExtractUser,
                Description => AuditTypes.NoDescription
                );

            Display.SetValue (Msg => Display.TokenUpdateFailed);

         end if;

      end if;
   end UpdateToken;


   ------------------------------------------------------------------
   -- ValidateEntry
   --
   -- Description:
   --    Validates user entry criteria.
   --    Performs all actions when Status = WaitingEntry.
   --
   -- Implementation Notes:
   --    None.
   --
   -- Traceunit : C.UserEntry.ValidateEntry
   -- Traceto : FD.UserEntry.EntryOK
   -- Traceto : FD.UserEntry.EntryNotAllowedC
   -- Traceto : FD.UserEntry.UserTokenTorn
   ------------------------------------------------------------------
   procedure ValidateEntry(TheStats : in out Stats.T)
   --# global in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in     Clock.CurrentTime;
   --#        in out UserToken.State;
   --#        in out Display.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#        in out TokenRemovalTimeout;
   --#           out Status;
   --# derives UserToken.State,
   --#         TheStats            from *,
   --#                                  UserToken.State &
   --#         Display.State,
   --#         TokenRemovalTimeout from *,
   --#                                  UserToken.State,
   --#                                  ConfigData.State,
   --#                                  Clock.CurrentTime &
   --#         AuditLog.State,
   --#         AuditLog.FileState  from UserToken.State,
   --#                                  Display.State,
   --#                                  AuditLog.State,
   --#                                  AuditLog.FileState,
   --#                                  ConfigData.State,
   --#                                  Clock.Now,
   --#                                  Clock.CurrentTime &
   --#         Status              from UserToken.State,
   --#                                  ConfigData.State,
   --#                                  Clock.CurrentTime;
   is

   begin

      if not UserToken.IsPresent then

         UserTokenTorn(TheStats => TheStats);

      else

         if ConfigData.IsInEntryPeriod
           ( Class   => UserToken.GetClass,
             TheTime => Clock.TheCurrentTime) then

            -- EntryOKC actions

            AuditLog.AddElementToLog
              ( ElementID   => AuditTypes.EntryPermitted,
                Severity    => AuditTypes.Information,
                User        => UserToken.ExtractUser,
                Description => AuditTypes.NoDescription
                );

            Display.SetValue (Msg => Display.OpenDoor);
            Status := WaitingRemoveTokenSuccess;


            TokenRemovalTimeout := Clock.AddDuration
              ( TheTime     => Clock.TheCurrentTime,
                TheDuration => ConfigData.TheTokenRemovalDuration );

         else

            -- EntryNotAllowedC actions

            AuditLog.AddElementToLog
              ( ElementID   => AuditTypes.EntryDenied,
                Severity    => AuditTypes.Warning,
                User        => UserToken.ExtractUser,
                Description => AuditTypes.NoDescription
                );

            Display.SetValue (Msg => Display.RemoveToken);
            Status := WaitingRemoveTokenFail;

         end if;

      end if;

   end ValidateEntry;


   ------------------------------------------------------------------
   -- UnlockDoor
   --
   -- Description:
   --    Waits for conditions to unlock the door.
   --    Performs all actions when Status = WaitingRemoveTokenSuccess.
   --
   -- Implementation Notes:
   --    None.
   --
   -- Traceunit : C.UserEntry.UnlockDoor
   -- Traceto : FD.UserEntry.UnlockDoorOK
   -- Traceto : FD.UserEntry.WaitingTokenRemoval
   -- Traceto : FD.UserEntry.TokenRemovalTimeout
   ------------------------------------------------------------------
   procedure UnlockDoor(TheStats : in out Stats.T)
   --# global in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in     Clock.CurrentTime;
   --#        in     TokenRemovalTimeout;
   --#        in out Status;
   --#        in out UserToken.State;
   --#        in out Display.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#        in out Door.State;
   --#        in out Latch.State;
   --# derives Status,
   --#         Display.State      from *,
   --#                                 UserToken.State,
   --#                                 Clock.CurrentTime,
   --#                                 TokenRemovalTimeout &
   --#         UserToken.State,
   --#         TheStats           from *,
   --#                                 UserToken.State &
   --#         AuditLog.State,
   --#         AuditLog.FileState from UserToken.State,
   --#                                 Display.State,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 ConfigData.State,
   --#                                 Clock.Now,
   --#                                 Clock.CurrentTime,
   --#                                 TokenRemovalTimeout,
   --#                                 Door.State,
   --#                                 Latch.State &
   --#         Door.State,
   --#         Latch.State        from *,
   --#                                 UserToken.State,
   --#                                 ConfigData.State,
   --#                                 Clock.CurrentTime,
   --#                                 Latch.State;
   --# pre Status = WaitingRemoveTokenSuccess and
   --#      --------------------------------------------------------
   --#      -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
   --#      --====================================================--
   --#      -- Before each call to UnlockDoor, the security       --
   --#      -- property holds.                                    --
   --#      --------------------------------------------------------
   --#      ( ( Latch.IsLocked(Latch.State) and
   --#          Door.TheCurrentDoor(Door.State) = Door.Open and
   --#          Clock.GreaterThanOrEqual(Clock.TheCurrentTime(Clock.CurrentTime),
   --#                                   Door.prf_alarmTimeout(Door.State)) ) <->
   --#        Door.TheDoorAlarm(Door.State) = AlarmTypes.Alarming );
   --#
   --# post
   --#      --------------------------------------------------------
   --#      -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
   --#      --====================================================--
   --#      -- After each call to UnlockDoor, the security        --
   --#      -- property holds.                                    --
   --#      --------------------------------------------------------
   --#      ( ( Latch.IsLocked(Latch.State) and
   --#          Door.TheCurrentDoor(Door.State) = Door.Open and
   --#          Clock.GreaterThanOrEqual(Clock.TheCurrentTime(Clock.CurrentTime),
   --#                                   Door.prf_alarmTimeout(Door.State)) ) <->
   --#        Door.TheDoorAlarm(Door.State) = AlarmTypes.Alarming ) and
   --#
   --#      ( ( Latch.IsLocked(Latch.State~) and
   --#          not Latch.IsLocked(Latch.State) )
   --#            <-> prf_UserEntryUnlockDoor );
   is

   begin

      if not UserToken.IsPresent then

         -- UnlockDoorOKC actions

         Door.UnlockDoor;
         UserToken.Clear;
         Display.SetValue (Msg => Display.DoorUnlocked);
         Status := Quiescent;

         Stats.AddSuccessfulEntry(TheStats => TheStats);

      else

         if Clock.GreaterThan(Clock.TheCurrentTime, TokenRemovalTimeout) then

            -- TokenRemovalTimeoutC actions

            AuditLog.AddElementToLog
              ( ElementID   => AuditTypes.EntryTimeout,
                Severity    => AuditTypes.Warning,
                User        => UserToken.ExtractUser,
                Description => AuditTypes.NoDescription
                );

            Display.SetValue (Msg => Display.RemoveToken);
            Status := WaitingRemoveTokenFail;

         else

            -- WaitingTokenRemovalC actions
            null;

         end if;

      end if;

   end UnlockDoor;


   ------------------------------------------------------------------
   -- FailedAccessTokenRemoved
   --
   -- Description:
   --    Handles the removal of a token after a failed access.
   --    Performs all actions when Status = WaitingRemoveTokenFail.
   --
   -- Implementation Notes:
   --    None
   --
   -- Traceunit : C.UserEntry.FailedAccessTokenRemoved
   -- Traceto: FD.UserEntry.FailedAccessTokenRemoved
   ------------------------------------------------------------------
   procedure FailedAccessTokenRemoved(TheStats : in out Stats.T)
   --# global in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in out UserToken.State;
   --#        in out Display.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#           out Status;
   --# derives UserToken.State,
   --#         Display.State,
   --#         TheStats           from * &
   --#         AuditLog.State,
   --#         AuditLog.FileState from UserToken.State,
   --#                                 Display.State,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 ConfigData.State,
   --#                                 Clock.Now &
   --#         Status             from ;
   is

   begin

      AuditLog.AddElementToLog
        ( ElementID   => AuditTypes.UserTokenRemoved,
          Severity    => AuditTypes.Information,
          User        => UserToken.ExtractUser,
          Description => AuditTypes.NoDescription
          );

      Display.SetValue (Msg => Display.Welcome);
      Status := Quiescent;

      Stats.AddFailedEntry (TheStats => TheStats);
      UserToken.Clear;

   end FailedAccessTokenRemoved;


   ------------------------------------------------------------------
   -- Public Operations
   ------------------------------------------------------------------


   ------------------------------------------------------------------
   -- InProgress
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   function InProgress return Boolean
   --# global Status;
   is
   begin
      return Status > Quiescent and Status < WaitingRemoveTokenFail;
   end InProgress;

   ------------------------------------------------------------------
   -- CurrentActivityPossible
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   function CurrentActivityPossible return Boolean
   --# global Status,
   --#        UserToken.State;
   --# return R =>
   --#        (R = ((Status > Quiescent and Status < WaitingRemoveTokenFail) or
   --#              (Status > Quiescent and not UserToken.IsPresent(UserToken.State))))
   --#        and (R -> Status > Quiescent)
   --#        and (R -> (Status = WaitingRemoveTokenFail ->
   --#                     not UserToken.IsPresent(UserToken.State)));
   is
   begin
      --# check InProgress(Status) <->
      --#         (Status > Quiescent and Status < WaitingRemoveTokenFail);
      --# check UserHasDeparted(Status, UserToken.State) <->
      --#         (Status > Quiescent and not UserToken.IsPresent(UserToken.State));
      return InProgress or UserHasDeparted;
   end CurrentActivityPossible;

   ------------------------------------------------------------------
   -- CanStart
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   function CanStart return Boolean
   --# global Status,
   --#        UserToken.State;
   is
   begin
      return Status = Quiescent and UserToken.IsPresent;
   end CanStart;

   ------------------------------------------------------------------
   -- DisplayPollUpdate
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure DisplayPollUpdate
   --# global in     Status;
   --#        in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in     Latch.State;
   --#        in out Display.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --# derives Display.State      from *,
   --#                                 Status,
   --#                                 Latch.State &
   --#         AuditLog.State     from *,
   --#                                 Status,
   --#                                 Display.State,
   --#                                 AuditLog.FileState,
   --#                                 ConfigData.State,
   --#                                 Clock.Now,
   --#                                 Latch.State &
   --#         AuditLog.FileState from *,
   --#                                 Status,
   --#                                 Display.State,
   --#                                 AuditLog.State,
   --#                                 ConfigData.State,
   --#                                 Clock.Now,
   --#                                 Latch.State;
   is
      NewMsg : Display.MsgT;
   begin
      if Latch.IsLocked then
         if Status = WaitingRemoveTokenFail then
            NewMsg := Display.RemoveToken;
         else
            NewMsg := Display.Welcome;
         end if;
         Display.ChangeDoorUnlockedMsg(Msg => NewMsg);
      end if;

   end DisplayPollUpdate;


   ------------------------------------------------------------------
   -- Progress
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure Progress
     (TheStats : in out Stats.T)
   --# global in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in     UserToken.Input;
   --#        in     Clock.CurrentTime;
   --#        in     KeyStore.Store;
   --#        in     KeyStore.State;
   --#        in     Bio.Input;
   --#        in out Status;
   --#        in out UserToken.State;
   --#        in out Display.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#        in out UserToken.Status;
   --#        in out FingerTimeout;
   --#        in out CertificateStore.FileState;
   --#        in out CertificateStore.State;
   --#        in out TokenRemovalTimeout;
   --#        in out Door.State;
   --#        in out Latch.State;
   --#           out UserToken.Output;
   --# derives UserToken.State,
   --#         UserToken.Status           from Status,
   --#                                         UserToken.State,
   --#                                         ConfigData.State,
   --#                                         UserToken.Status,
   --#                                         UserToken.Input,
   --#                                         Clock.CurrentTime,
   --#                                         KeyStore.Store,
   --#                                         KeyStore.State,
   --#                                         CertificateStore.State &
   --#         AuditLog.State,
   --#         AuditLog.FileState         from Status,
   --#                                         UserToken.State,
   --#                                         Display.State,
   --#                                         AuditLog.State,
   --#                                         AuditLog.FileState,
   --#                                         ConfigData.State,
   --#                                         Clock.Now,
   --#                                         UserToken.Status,
   --#                                         UserToken.Input,
   --#                                         Clock.CurrentTime,
   --#                                         KeyStore.Store,
   --#                                         KeyStore.State,
   --#                                         FingerTimeout,
   --#                                         Bio.Input,
   --#                                         CertificateStore.FileState,
   --#                                         CertificateStore.State,
   --#                                         TokenRemovalTimeout,
   --#                                         Door.State,
   --#                                         Latch.State &
   --#         CertificateStore.FileState,
   --#         CertificateStore.State     from *,
   --#                                         Status,
   --#                                         UserToken.State,
   --#                                         ConfigData.State,
   --#                                         UserToken.Status,
   --#                                         Clock.CurrentTime,
   --#                                         KeyStore.Store,
   --#                                         KeyStore.State,
   --#                                         CertificateStore.State &
   --#         TokenRemovalTimeout,
   --#         Latch.State                from *,
   --#                                         Status,
   --#                                         UserToken.State,
   --#                                         ConfigData.State,
   --#                                         Clock.CurrentTime &
   --#         Status                     from *,
   --#                                         UserToken.State,
   --#                                         ConfigData.State,
   --#                                         UserToken.Status,
   --#                                         UserToken.Input,
   --#                                         Clock.CurrentTime,
   --#                                         KeyStore.Store,
   --#                                         KeyStore.State,
   --#                                         FingerTimeout,
   --#                                         Bio.Input,
   --#                                         TokenRemovalTimeout &
   --#         Display.State              from *,
   --#                                         Status,
   --#                                         UserToken.State,
   --#                                         ConfigData.State,
   --#                                         UserToken.Status,
   --#                                         UserToken.Input,
   --#                                         Clock.CurrentTime,
   --#                                         KeyStore.Store,
   --#                                         KeyStore.State,
   --#                                         FingerTimeout,
   --#                                         Bio.Input,
   --#                                         CertificateStore.State,
   --#                                         TokenRemovalTimeout &
   --#         TheStats                   from *,
   --#                                         Status,
   --#                                         UserToken.State,
   --#                                         ConfigData.State,
   --#                                         Bio.Input &
   --#         FingerTimeout              from *,
   --#                                         Status,
   --#                                         UserToken.State,
   --#                                         ConfigData.State,
   --#                                         UserToken.Status,
   --#                                         UserToken.Input,
   --#                                         Clock.CurrentTime,
   --#                                         KeyStore.Store,
   --#                                         KeyStore.State &
   --#         UserToken.Output           from Status,
   --#                                         UserToken.State,
   --#                                         ConfigData.State,
   --#                                         UserToken.Status,
   --#                                         Clock.CurrentTime,
   --#                                         KeyStore.Store,
   --#                                         KeyStore.State,
   --#                                         CertificateStore.State &
   --#         Door.State                 from *,
   --#                                         Status,
   --#                                         UserToken.State,
   --#                                         ConfigData.State,
   --#                                         Clock.CurrentTime,
   --#                                         Latch.State;
   --# pre Keystore.PrivateKeyPresent(KeyStore.State) and
   --#     Status > Quiescent
   --#     and (Status = WaitingRemoveTokenFail
   --#             -> not UserToken.IsPresent(UserToken.State)) and
   --#      --------------------------------------------------------
   --#      -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
   --#      --====================================================--
   --#      -- Before each call to Progress, the security         --
   --#      -- property holds.                                    --
   --#      --------------------------------------------------------
   --#      ( ( Latch.IsLocked(Latch.State) and
   --#          Door.TheCurrentDoor(Door.State) = Door.Open and
   --#          Clock.GreaterThanOrEqual(Clock.TheCurrentTime(Clock.CurrentTime),
   --#                                   Door.prf_alarmTimeout(Door.State)) ) <->
   --#        Door.TheDoorAlarm(Door.State) = AlarmTypes.Alarming );
   --#
   --# post
   --#      --------------------------------------------------------
   --#      -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
   --#      --====================================================--
   --#      -- After each call to Progress, the security property --
   --#      -- holds.                                             --
   --#      --------------------------------------------------------
   --#      ( ( Latch.IsLocked(Latch.State) and
   --#          Door.TheCurrentDoor(Door.State) = Door.Open and
   --#          Clock.GreaterThanOrEqual(Clock.TheCurrentTime(Clock.CurrentTime),
   --#                                   Door.prf_alarmTimeout(Door.State)) ) <->
   --#        Door.TheDoorAlarm(Door.State) = AlarmTypes.Alarming ) and
   --#
   --#      ( ( Latch.IsLocked(Latch.State~) and
   --#          not Latch.IsLocked(Latch.State) )
   --#            <-> prf_UserEntryUnlockDoor );
   is
      subtype ActiveStatusT is StatusT
        range GotUserToken .. WaitingRemoveTokenFail;

      LocalStatus : ActiveStatusT;

   begin
      LocalStatus := ActiveStatusT'(Status);

      case LocalStatus is
         when GotUserToken =>
            ValidateUserToken (TheStats => TheStats);
         when WaitingFinger =>
            ReadFinger (TheStats => TheStats);
         when GotFinger =>
            ValidateFinger (TheStats => TheStats);
         when WaitingUpdateToken =>
            UpdateToken (TheStats => TheStats);
         when WaitingEntry =>
            ValidateEntry (TheStats => TheStats);
         when WaitingRemoveTokenSuccess =>
            UnlockDoor (TheStats => TheStats);
         when WaitingRemoveTokenFail =>
            FailedAccessTokenRemoved (TheStats => TheStats);
      end case;

   end Progress;


   ------------------------------------------------------------------
   -- StartEntry
   --
   -- Implementation Notes:
   --    The physical reading of the certificates from the token is
   --    postponed until validation since only as many certificates as are
   --    required to do this validation are read from the token.
   ------------------------------------------------------------------
   procedure StartEntry
   --# global in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in out Display.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#           out Status;
   --# derives Status             from  &
   --#         Display.State      from * &
   --#         AuditLog.State     from *,
   --#                                 Display.State,
   --#                                 AuditLog.FileState,
   --#                                 ConfigData.State,
   --#                                 Clock.Now &
   --#         AuditLog.FileState from *,
   --#                                 Display.State,
   --#                                 AuditLog.State,
   --#                                 ConfigData.State,
   --#                                 Clock.Now;
   is

   begin

      Display.SetValue (Msg => Display.Wait);
      Status := GotUserToken;

   end StartEntry;

end UserEntry;
