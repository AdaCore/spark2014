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
-- Implementation Notes:
--    Implements UserEntry
--
------------------------------------------------------------------

with CommonTypes;
use type CommonTypes.PresenceT;

with IandATypes;
use type IandATypes.MatchResultT;
use type IandATypes.FarT;

with AlarmTypes,
     Door;

use AlarmTypes,
    Door;

package body UserEntry
  with Refined_State => (State => (Status,
                                   FingerTimeout,
                                   TokenRemovalTimeout))
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
   function UserHasDeparted return Boolean is
     (Status > Quiescent and not UserToken.IsPresent)
     with Global  => (Status,
                      UserToken.State);

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
   procedure UserTokenTorn (TheStats : in out Stats.T)
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State),
                      Output => Status,
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 Display.State,
                                 UserToken.State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Display.State,
                                               UserToken.State),
                      (Display.State,
                       TheStats,
                       UserToken.State)    =>+ null,
                      Status                => null)
   is
   begin

      AuditLog.AddElementToLog
        (ElementID   => AuditTypes.UserTokenRemoved,
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
   procedure ValidateUserToken (TheStats : in out Stats.T)
     with Global  => (Input  => (Bio.Input,
                                 Clock.CurrentTime,
                                 Clock.Now,
                                 ConfigData.State,
                                 KeyStore.State,
                                 KeyStore.Store,
                                 UserToken.Input),
                      Output => Status,
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 Display.State,
                                 FingerTimeout,
                                 UserToken.State,
                                 UserToken.Status)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.CurrentTime,
                                               Clock.Now,
                                               ConfigData.State,
                                               Display.State,
                                               KeyStore.State,
                                               KeyStore.Store,
                                               UserToken.Input,
                                               UserToken.State,
                                               UserToken.Status),
                      (Display.State,
                       UserToken.State,
                       UserToken.Status)   =>+ (Clock.CurrentTime,
                                                KeyStore.State,
                                                KeyStore.Store,
                                                UserToken.Input,
                                                UserToken.State,
                                                UserToken.Status),
                      FingerTimeout        =>+ (Clock.CurrentTime,
                                                ConfigData.State,
                                                KeyStore.State,
                                                KeyStore.Store,
                                                UserToken.Input,
                                                UserToken.State,
                                                UserToken.Status),
                      Status               => (Clock.CurrentTime,
                                               KeyStore.State,
                                               KeyStore.Store,
                                               UserToken.Input,
                                               UserToken.State,
                                               UserToken.Status),
                      TheStats             =>+ UserToken.State,
                      null                 => Bio.Input)
   is
     AuthCertOK  : Boolean;
     TokenOK     : Boolean;

     Description : AuditTypes.DescriptionT;
   begin

      if not UserToken.IsPresent then

         UserTokenTorn(TheStats => TheStats);

      else

         UserToken.ReadAndCheckAuthCert (AuthCertOK => AuthCertOK);

         if AuthCertOK then

            -- GetPresentUserTokenC postponed actions

            AuditLog.AddElementToLog
              (ElementID   => AuditTypes.UserTokenPresent,
               Severity    => AuditTypes.Information,
               User        => UserToken.ExtractUser,
               Description => AuditTypes.NoDescription
               );

            -- BioCheckNotRequiredC actions

            AuditLog.AddElementToLog
              (ElementID   => AuditTypes.AuthCertValid,
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
                 (ElementID   => AuditTypes.UserTokenPresent,
                  Severity    => AuditTypes.Information,
                  User        => UserToken.ExtractUser,
                  Description => AuditTypes.NoDescription
                  );

               -- BioCheckRequiredC actions

               AuditLog.AddElementToLog
                 (ElementID   => AuditTypes.AuthCertInvalid,
                  Severity    => AuditTypes.Information,
                  User        => UserToken.ExtractUser,
                  Description => AuditTypes.NoDescription
                  );

               Display.SetValue (Msg => Display.InsertFinger);
               Status := WaitingFinger;

               FingerTimeout := Clock.AddDuration
                 (TheTime     => Clock.TheCurrentTime,
                  TheDuration => ConfigData.TheFingerWaitDuration );

               -- Flush any stale BIO data.
               Bio.Flush;

            else
               -- GetPresentUserTokenC postponed actions

               AuditLog.AddElementToLog
                 (ElementID   => AuditTypes.UserTokenPresent,
                  Severity    => AuditTypes.Information,
                  User        => UserToken.ExtractUser,
                  Description => AuditTypes.NoDescription
                  );


               -- ValidateUserTokenFailC actions

               AuditLog.AddElementToLog
                 (ElementID   => AuditTypes.UserTokenInvalid,
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
   procedure ReadFinger (TheStats : in out Stats.T)
     with Global  => (Input  => (Bio.Input,
                                 Clock.CurrentTime,
                                 Clock.Now,
                                 ConfigData.State,
                                 FingerTimeout),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 Display.State,
                                 Status,
                                 UserToken.State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Bio.Input,
                                               Clock.CurrentTime,
                                               Clock.Now,
                                               ConfigData.State,
                                               Display.State,
                                               FingerTimeout,
                                               UserToken.State),
                      (Display.State,
                       Status)             =>+ (Bio.Input,
                                                Clock.CurrentTime,
                                                FingerTimeout,
                                                UserToken.State),
                      (TheStats,
                       UserToken.State)    =>+ UserToken.State),
          Pre     => Status = WaitingFinger
   is
      FingerPresence : CommonTypes.PresenceT;
   begin

      if not UserToken.IsPresent then

         UserTokenTorn(TheStats => TheStats);

      else

         if Clock.GreaterThan(Clock.TheCurrentTime, FingerTimeout) then

            -- FingerTimeoutC actions

            AuditLog.AddElementToLog
              (ElementID   => AuditTypes.FingerTimeout,
               Severity    => AuditTypes.Warning,
               User        => UserToken.ExtractUser,
               Description => AuditTypes.NoDescription
               );

            Display.SetValue (Msg => Display.RemoveToken);
            Status := WaitingRemoveTokenFail;

         else

            Bio.Poll(FingerPresent => FingerPresence);

            if FingerPresence = CommonTypes.Present then

               -- ReadFingerOKC actions

               AuditLog.AddElementToLog
                 (ElementID   => AuditTypes.FingerDetected,
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
     with Global  => (Input  => (Bio.Input,
                                 Clock.Now,
                                 ConfigData.State),
                      Output => Status,
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 Display.State,
                                 UserToken.State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Bio.Input,
                                               Clock.Now,
                                               ConfigData.State,
                                               Display.State,
                                               UserToken.State),
                      (Display.State,
                       TheStats)           =>+ (Bio.Input,
                                                ConfigData.State,
                                                UserToken.State),
                      Status               => (Bio.Input,
                                               ConfigData.State,
                                               UserToken.State),
                      UserToken.State      =>+ null)
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
        with Global => AchievedFAR
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
           with Global  => (Input  => AchievedFAR,
                            In_Out => Result),
                Depends => (Result =>+ AchievedFAR)
         is
            FullString : String := "Acheived FAR : "
              & IandATypes.FarT_Image(AchievedFAR) ;
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
   procedure UpdateToken (TheStats : in out Stats.T)
     with Global  => (Input  => (Clock.CurrentTime,
                                 Clock.Now,
                                 ConfigData.State,
                                 KeyStore.State,
                                 KeyStore.Store),
                      Output => Status,
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 CertificateStore.FileState,
                                 CertificateStore.State,
                                 Display.State,
                                 UserToken.Output,
                                 UserToken.State,
                                 UserToken.Status)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State) => (AuditLog.FileState,
                                           AuditLog.State,
                                           CertificateStore.FileState,
                                           CertificateStore.State,
                                           Clock.CurrentTime,
                                           Clock.Now,
                                           ConfigData.State,
                                           Display.State,
                                           KeyStore.State,
                                           KeyStore.Store,
                                           UserToken.State,
                                           UserToken.Status),

                      (CertificateStore.FileState,
                       CertificateStore.State,
                       Display.State,
                       UserToken.Status) =>+ (CertificateStore.State,
                                              Clock.CurrentTime,
                                              ConfigData.State,
                                              KeyStore.State,
                                              KeyStore.Store,
                                              UserToken.State,
                                              UserToken.Status),

                      Status => UserToken.State,

                      TheStats =>+ UserToken.State,

                      UserToken.Output =>+ (CertificateStore.State,
                                            Clock.CurrentTime,
                                            ConfigData.State,
                                            KeyStore.State,
                                            KeyStore.Store,
                                            UserToken.State,
                                            UserToken.Status),

                      UserToken.State =>+ (CertificateStore.State,
                                           Clock.CurrentTime,
                                           ConfigData.State,
                                           KeyStore.State)),
          Pre     => Keystore.PrivateKeyPresent
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
              (ElementID   => AuditTypes.AuthCertWritten,
               Severity    => AuditTypes.Information,
               User        => UserToken.ExtractUser,
               Description => AuditTypes.NoDescription
               );

            Display.SetValue (Msg => Display.Wait);

            CertificateStore.UpdateStore;

         else

            -- WriteUserTokenFailC actions

            AuditLog.AddElementToLog
              (ElementID   => AuditTypes.AuthCertWriteFailed,
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
   procedure ValidateEntry (TheStats : in out Stats.T)
     with Global  => (Input  => (Clock.CurrentTime,
                                 Clock.Now,
                                 ConfigData.State),
                      Output => Status,
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 Display.State,
                                 TokenRemovalTimeout,
                                 UserToken.State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)      => (AuditLog.FileState,
                                                AuditLog.State,
                                                Clock.CurrentTime,
                                                Clock.Now,
                                                ConfigData.State,
                                                Display.State,
                                                UserToken.State),
                      (Display.State,
                       TokenRemovalTimeout) =>+ (Clock.CurrentTime,
                                                 ConfigData.State,
                                                 UserToken.State),
                      Status                => (Clock.CurrentTime,
                                                ConfigData.State,
                                                UserToken.State),
                      (TheStats,
                       UserToken.State)     =>+ UserToken.State)
   is
   begin

      if not UserToken.IsPresent then

         UserTokenTorn(TheStats => TheStats);

      else

         if ConfigData.IsInEntryPeriod
           (Class   => UserToken.GetClass,
            TheTime => Clock.TheCurrentTime) then

            -- EntryOKC actions

            AuditLog.AddElementToLog
              (ElementID   => AuditTypes.EntryPermitted,
               Severity    => AuditTypes.Information,
               User        => UserToken.ExtractUser,
               Description => AuditTypes.NoDescription
               );

            Display.SetValue (Msg => Display.OpenDoor);
            Status := WaitingRemoveTokenSuccess;


            TokenRemovalTimeout := Clock.AddDuration
              (TheTime     => Clock.TheCurrentTime,
               TheDuration => ConfigData.TheTokenRemovalDuration );

         else

            -- EntryNotAllowedC actions

            AuditLog.AddElementToLog
              (ElementID   => AuditTypes.EntryDenied,
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
     with Global  => (Input  => (Clock.CurrentTime,
                                 Clock.Now,
                                 ConfigData.State,
                                 TokenRemovalTimeout),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 Display.State,
                                 Door.State,
                                 Latch.State,
                                 Status,
                                 UserToken.State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.CurrentTime,
                                               Clock.Now,
                                               ConfigData.State,
                                               Display.State,
                                               Door.State,
                                               Latch.State,
                                               TokenRemovalTimeout,
                                               UserToken.State),
                      (Display.State,
                       Status)             =>+ (Clock.CurrentTime,
                                                TokenRemovalTimeout,
                                                UserToken.State),
                      (Door.State,
                       Latch.State)        =>+ (Clock.CurrentTime,
                                                ConfigData.State,
                                                Latch.State,
                                                UserToken.State),
                      (TheStats,
                       UserToken.State)    =>+ UserToken.State),

          Pre     =>
            Status = WaitingRemoveTokenSuccess and
            --------------------------------------------------------
            -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
            --====================================================--
            -- Before each call to UnlockDoor, the security       --
            -- property holds.                                    --
            --------------------------------------------------------
            ((Latch.IsLocked and
                Door.TheCurrentDoor = Door.Open and
                Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
                                         Door.Alarm_Timeout)) =
               (Door.TheDoorAlarm = AlarmTypes.Alarming)),

          Post    =>
            --------------------------------------------------------
            -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
            --====================================================--
            -- After each call to UnlockDoor, the security        --
            -- property holds.                                    --
            --------------------------------------------------------
            ((Latch.IsLocked and
                Door.TheCurrentDoor = Door.Open and
                Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
                                         Door.alarm_Timeout)) =
               (Door.TheDoorAlarm = AlarmTypes.Alarming))



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
              (ElementID   => AuditTypes.EntryTimeout,
               Severity    => AuditTypes.Warning,
               User        => UserToken.ExtractUser,
               Description => AuditTypes.NoDescription);

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
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State),
                      Output => Status,
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 Display.State,
                                 UserToken.State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Display.State,
                                               UserToken.State),
                      (Display.State,
                       TheStats,
                       UserToken.State)    =>+ null,
                      Status               => null)
   is
   begin
      AuditLog.AddElementToLog
        (ElementID   => AuditTypes.UserTokenRemoved,
         Severity    => AuditTypes.Information,
         User        => UserToken.ExtractUser,
         Description => AuditTypes.NoDescription);

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
   function InProgress return Boolean is
     (Status > Quiescent and Status < WaitingRemoveTokenFail)
     with Refined_Global  => Status;

   ------------------------------------------------------------------
   -- CurrentActivityPossible
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   function CurrentActivityPossible return Boolean is
     (InProgress or UserHasDeparted)
     with Refined_Global => (Status,
                             UserToken.State);

   ------------------------------------------------------------------
   -- CanStart
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   function CanStart return Boolean is
     (Status = Quiescent and UserToken.IsPresent)
     with Refined_Global => (Status,
                             UserToken.State);

   ------------------------------------------------------------------
   -- DisplayPollUpdate
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure DisplayPollUpdate
     with Refined_Global  => (Input  => (Clock.Now,
                                         ConfigData.State,
                                         Latch.State,
                                         Status),
                              In_Out => (AuditLog.FileState,
                                         AuditLog.State,
                                         Display.State)),
          Refined_Depends => ((AuditLog.FileState,
                               AuditLog.State)     => (AuditLog.FileState,
                                                       AuditLog.State,
                                                       Clock.Now,
                                                       ConfigData.State,
                                                       Display.State,
                                                       Latch.State,
                                                       Status),
                              Display.State        =>+ (Latch.State,
                                                        Status))
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
   procedure Progress (TheStats : in out Stats.T)
     with Refined_Global  => (Input  => (Bio.Input,
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
                                         FingerTimeout,
                                         Latch.State,
                                         Status,
                                         TokenRemovalTimeout,
                                         UserToken.Output,
                                         UserToken.State,
                                         UserToken.Status)),
          Refined_Depends => ((AuditLog.FileState,
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
                                                   FingerTimeout,
                                                   KeyStore.State,
                                                   KeyStore.Store,
                                                   Latch.State,
                                                   Status,
                                                   TokenRemovalTimeout,
                                                   UserToken.Input,
                                                   UserToken.State,
                                                   UserToken.Status),

                              (CertificateStore.FileState,
                               CertificateStore.State) =>+
                                      (CertificateStore.State,
                                       Clock.CurrentTime,
                                       ConfigData.State,
                                       KeyStore.State,
                                       KeyStore.Store,
                                       Status,
                                       UserToken.State,
                                       UserToken.Status),

                              Display.State =>+ (Bio.Input,
                                                 CertificateStore.State,
                                                 Clock.CurrentTime,
                                                 ConfigData.State,
                                                 FingerTimeout,
                                                 KeyStore.State,
                                                 KeyStore.Store,
                                                 Status,
                                                 TokenRemovalTimeout,
                                                 UserToken.Input,
                                                 UserToken.State,
                                                 UserToken.Status),

                              (Door.State,
                               Latch.State) =>+ (Clock.CurrentTime,
                                                 ConfigData.State,
                                                 Latch.State,
                                                 Status,
                                                 UserToken.State),

                              FingerTimeout =>+ (Clock.CurrentTime,
                                                 ConfigData.State,
                                                 KeyStore.State,
                                                 KeyStore.Store,
                                                 Status,
                                                 UserToken.Input,
                                                 UserToken.State,
                                                 UserToken.Status),

                              Status =>+ (Bio.Input,
                                          Clock.CurrentTime,
                                          ConfigData.State,
                                          FingerTimeout,
                                          KeyStore.State,
                                          KeyStore.Store,
                                          TokenRemovalTimeout,
                                          UserToken.Input,
                                          UserToken.State,
                                          UserToken.Status),

                              TheStats =>+ (Bio.Input,
                                            ConfigData.State,
                                            Status,
                                            UserToken.State),

                              TokenRemovalTimeout =>+ (Clock.CurrentTime,
                                                       ConfigData.State,
                                                       Status,
                                                       UserToken.State),

                              UserToken.Output =>+ (CertificateStore.State,
                                                    Clock.CurrentTime,
                                                    ConfigData.State,
                                                    KeyStore.State,
                                                    KeyStore.Store,
                                                    Status,
                                                    UserToken.State,
                                                    UserToken.Status),

                              (UserToken.State,
                               UserToken.Status) => (CertificateStore.State,
                                                     Clock.CurrentTime,
                                                     ConfigData.State,
                                                     KeyStore.State,
                                                     KeyStore.Store,
                                                     Status,
                                                     UserToken.Input,
                                                     UserToken.State,
                                                     UserToken.Status)),
          --------------------------------------------------------
          -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
          --====================================================--
          -- Before each call to Progress, the security         --
          -- property holds.                                    --
          --------------------------------------------------------
          --  Refined_Pre     => Keystore.PrivateKeyPresent and then
          --                       Status > Quiescent and then
          --                       ((Status = WaitingRemoveTokenFail)
          --                        <= not UserToken.IsPresent) and then

          --                       ((Latch.IsLocked and then
          --                           Door.TheCurrentDoor = Door.Open and then
          --                           Clock.GreaterThanOrEqual
          --                             (Clock.TheCurrentTime,
          --                              Door.alarm_Timeout)) =
          --                          (Door.TheDoorAlarm = AlarmTypes.Alarming))
          --------------------------------------------------------
          -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
          --====================================================--
          -- After each call to Progress, the security property --
          -- holds.                                             --
          --------------------------------------------------------
          Refined_Post    =>
            ((Latch.IsLocked and
                Door.TheCurrentDoor = Door.Open and
                Clock.GreaterThanOrEqual (Clock.TheCurrentTime,
                                          Door.alarm_Timeout)) =
               (Door.TheDoorAlarm = AlarmTypes.Alarming))



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
     with Refined_Global  => (Input  => (Clock.Now,
                                         ConfigData.State),
                              Output => Status,
                              In_Out => (AuditLog.FileState,
                                         AuditLog.State,
                                         Display.State)),
          Refined_Depends => ((AuditLog.FileState,
                               AuditLog.State)     => (AuditLog.FileState,
                                                       AuditLog.State,
                                                       Clock.Now,
                                                       ConfigData.State,
                                                       Display.State),
                              Display.State        =>+ null,
                              Status               => null)
   is
   begin
      Display.SetValue (Msg => Display.Wait);
      Status := GotUserToken;
   end StartEntry;

end UserEntry;
