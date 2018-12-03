------------------------------------------------------------------
-- Tokeneer ID Station Core Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency.All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd.under contract to the National Security Agency.
------------------------------------------------------------------

------------------------------------------------------------------
-- TokenReader
--
-- Implementation Notes:
--     None.
--
------------------------------------------------------------------
with TokenReader.Interfac;
use type TokenReader.Interfac.ReaderStateT;

with AuditTypes;
with AuditLog;

with TokenTypes;
use type TokenTypes.TryT;

with CommonTypes;
use type CommonTypes.Unsigned32T;

package body TokenReader
  with Refined_State => (State  => ReaderStatus,
                         Status => TokenReader.Interfac.ReaderStatus,
                         Input  => TokenReader.Interfac.ReaderInput,
                         Output => TokenReader.Interfac.ReaderOutput)
is
   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   type ReaderInfoT is record
      Name           : Interfac.ReaderNameT;
      TokenTry       : TokenTypes.TryT;
      TokenID        : TokenTypes.TokenIDT;
      TokenConnected : Boolean;
      TokenHandle    : Interfac.CardHandleT;
      CurrentStatus  : Interfac.ValidReaderStateT;
      LastFault      : CommonTypes.Unsigned32T;
   end record;

   NoReaderInfo : constant ReaderInfoT :=
     ReaderInfoT'(Name           => "UNKNOWN ",
                  TokenTry       => TokenTypes.NoToken,
                  TokenID        => TokenTypes.TokenIDT'First,
                  TokenConnected => False,
                  TokenHandle    => Interfac.NullHandle,
                  CurrentStatus  => Interfac.Unaware,
                  LastFault      => CommonTypes.Unsigned32T'First);

   type ReaderInfoArrayT is array (ReaderT) of ReaderInfoT;

   NoReaders : constant ReaderInfoArrayT :=
     ReaderInfoArrayT'(others => NoReaderInfo);

   type ReaderNameArrayT is array (ReaderT) of Interfac.ReaderNameT;

   ExpectedReaderNames : constant ReaderNameArrayT :=
     ReaderNameArrayT'(User  => "EXTREAD ",
                       Admin => "INTREAD ");


   ------------------------------------------------------------------
   -- State
   --
   ------------------------------------------------------------------
   ReaderStatus : ReaderInfoArrayT;


   ------------------------------------------------------------------
   -- Private Operations
   ------------------------------------------------------------------
   ------------------------------------------------------------------
   -- GetResponseCode
   --
   -- Description:
   --    Converts a supplied numeric response code to the
   --    correct enumeration.
   --
   -- Implementation Notes:
   --    None
   ------------------------------------------------------------------
   function GetResponseCode (ResponseCode : CommonTypes.Unsigned32T)
                            return Interfac.ResponseCodeT
   is (if ResponseCode >=
            Interfac.ResponseCodeT'Pos(Interfac.ResponseCodeT'First)
         and ResponseCode <=
               Interfac.ResponseCodeT'Pos(Interfac.ResponseCodeT'Last)
       then Interfac.ResponseCodeT'Val(ResponseCode)
       else Interfac.InvalidResponseCode);

   ------------------------------------------------------------------
   -- GetReaderState
   --
   -- Description:
   --    Converts a supplied numeric reader state to the
   --    correct enumeration.
   --
   -- Implementation Notes:
   --    None
   ------------------------------------------------------------------
   function GetReaderState (ReaderState : CommonTypes.Unsigned32T)
                           return Interfac.ReaderStateT
   is (if ReaderState >=
            Interfac.ReaderStateT'Pos(Interfac.ReaderStateT'First)
         and ReaderState <=
               Interfac.ReaderStateT'Pos(Interfac.ReaderStateT'Last)
       then Interfac.ReaderStateT'Val(ReaderState)
       else Interfac.InvalidReaderState);

   ------------------------------------------------------------------
   -- GetCardState
   --
   -- Description:
   --    Converts a supplied numeric card state to the
   --    correct enumeration.
   --
   -- Implementation Notes:
   --    None
   ------------------------------------------------------------------
   function GetCardState (CardState : CommonTypes.Unsigned32T)
                         return Interfac.CardStateT
   is (if CardState >=
            Interfac.CardStateT'Pos(Interfac.CardStateT'First)
         and CardState <=
               Interfac.CardStateT'Pos(Interfac.CardStateT'Last)
       then Interfac.CardStateT'Val(CardState)
       else Interfac.InvalidCardState);

   ------------------------------------------------------------------
   -- MakeDescription
   --
   -- Description:
   --    Produces a description for the Audit log from the
   --    supplied text and response code.
   --
   -- Implementation Notes:
   --    None
   ------------------------------------------------------------------
   function MakeDescription
     (Text         : CommonTypes.StringF1L1000;
      ResponseCode : CommonTypes.Unsigned32T) return AuditTypes.DescriptionT
   with Pre => True  --  no contextual analysis needed
   is
      Result : AuditTypes.DescriptionT := AuditTypes.NoDescription;
      TheCodeName : Interfac.ResponseCodeT;

      ------------------------------------------------------------------
      -- SetResultString
      --
      -- Description:
      --    Sets the Result string allowing for overflow.
      --
      -- Implementation Notes:
      --    None
      ------------------------------------------------------------------
      procedure SetResultString
        with Global  => (Input  => (ResponseCode,
                                    Text,
                                    TheCodeName),
                         In_Out => Result),
             Depends => (Result =>+ (ResponseCode,
                                     Text,
                                     TheCodeName))
      is
         FullString : constant String := Text & ": "
           & Interfac.ResponseCodeT_Image(TheCodeName)& " ("
           & CommonTypes.Unsigned32T_Image(ResponseCode)& ")";
      begin
         -- if the Full string is shorter then use it all otherwise
         -- truncate it.
         if FullString'Last <= AuditTypes.DescriptionI'Last then
            Result (1 .. FullString'Last) := FullString;
         else
            Result := FullString (1 .. AuditTypes.DescriptionI'Last);
         end if;
      end SetResultString;

   begin
      TheCodeName := GetResponseCode (ResponseCode);
      SetResultString;
      return Result;
   end MakeDescription;

   ------------------------------------------------------------------
   -- Public Operations
   ------------------------------------------------------------------

   ------------------------------------------------------------------
   -- Init
   --
   -- Implementation Notes:
   --    This routine gets a list of the available readers
   --    it raises an error if the required readers are not present.
   ------------------------------------------------------------------
   procedure Init
     with Refined_Global  => (Input  => (Clock.Now,
                                         ConfigData.State,
                                         Interfac.ReaderStatus),
                              Output => ReaderStatus,
                              In_Out => (AuditLog.FileState,
                                         AuditLog.State)),
          Refined_Depends => ((AuditLog.FileState,
                               AuditLog.State) => (AuditLog.FileState,
                                                   AuditLog.State,
                                                   Clock.Now,
                                                   ConfigData.State,
                                                   Interfac.ReaderStatus),
                              ReaderStatus => Interfac.ReaderStatus)
   is
      NumberReaders : CommonTypes.Unsigned32T;
      ResponseCode  : CommonTypes.Unsigned32T;
      Readers       : Interfac.ReaderNameArrayT;

      ------------------------------------------------------------------
      -- SetReaderName
      --
      -- Description:
      --    Sets the Reader's name to the provided value.
      --
      -- Implementation Notes:
      --    Presented as a subroutine to aid VCG.
      ------------------------------------------------------------------
      procedure SetReaderName (TheReader : in ReaderT;
                               TheName   : in Interfac.ReaderNameT)
        with Global  => (In_Out => ReaderStatus),
             Depends => (ReaderStatus =>+ (TheName,
                                           TheReader))
      is
      begin
         ReaderStatus(TheReader).Name := TheName;
      end SetReaderName;

      ------------------------------------------------------------------
      -- Clears all reader information.
      --
      -- Description:
      --    Sets the Reader's name to the provided value.
      --
      -- Implementation Notes:
      --    Presented as a subroutine to aid VCG.
      ------------------------------------------------------------------
      procedure ClearReaders
        with Global  => (Output => ReaderStatus),
             Depends => (ReaderStatus => null)
      is
      begin
         ReaderStatus := NoReaders;
      end ClearReaders;

   -----------------------------------------------------------------
   -- begin Init
   -----------------------------------------------------------------
   begin

      ClearReaders;

      -- We are looking for 2 readers.
      NumberReaders := 2;
      Interfac.ListReaders(List         => Readers,
                           Number       => NumberReaders,
                           ResponseCode => ResponseCode);

      if ResponseCode = Interfac.ResponseCodeT'Pos(Interfac.Success) then

         if NumberReaders >=
              CommonTypes.Unsigned32T(Interfac.ReaderArrayI'First) and
           NumberReaders <=
             CommonTypes.Unsigned32T(Interfac.ReaderArrayI'Last)
         then
            for I in Interfac.ReaderArrayI
              range 1..Interfac.ReaderArrayI(NumberReaders)
            loop
               pragma Loop_Invariant
                 (I <= Interfac.ReaderArrayI(NumberReaders) and
                  NumberReaders = NumberReaders'Loop_Entry);
               for R in ReaderT loop
                  pragma Loop_Invariant
                    (I <= Interfac.ReaderArrayI(NumberReaders) and
                     NumberReaders = NumberReaders'Loop_Entry);

                  if ExpectedReaderNames(R) = Readers(I) then
                     SetReaderName(TheReader => R,
                                   TheName   => Readers(I));
                     exit;
                  end if;
               end loop;
            end loop;

            if ReaderStatus(User).Name /= ExpectedReaderNames(User) then

               AuditLog.AddElementToLog
                 (ElementID   => AuditTypes.SystemFault,
                  Severity    => AuditTypes.Warning,
                  User        => AuditTypes.NoUser,
                  Description => "Token Reader initialisation failure : " &
                    "External token reader not found");

            end if;

            if ReaderStatus(Admin).Name /= ExpectedReaderNames(Admin) then

               AuditLog.AddElementToLog
                 (ElementID   => AuditTypes.SystemFault,
                  Severity    => AuditTypes.Warning,
                  User        => AuditTypes.NoUser,
                  Description => "Token Reader initialisation failure : " &
                    "Internal token reader not found");

            end if;

         else

            AuditLog.AddElementToLog
              (ElementID   => AuditTypes.SystemFault,
               Severity    => AuditTypes.Warning,
               User        => AuditTypes.NoUser,
               Description => "Token Reader initialisation failure : " &
                 "Invalid Number of Token Readers found");

         end if;

      else

         AuditLog.AddElementToLog
           (ElementID   => AuditTypes.SystemFault,
            Severity    => AuditTypes.Warning,
            User        => AuditTypes.NoUser,
            Description =>
              MakeDescription("Token Reader initialisation failure : ",
                              ResponseCode));

      end if;

   end Init;

   ------------------------------------------------------------------
   -- Poll
   --
   -- Implementation Notes:
   --    This logs a system fault of we can't obtain a sensible
   --    reader status.
   ------------------------------------------------------------------
   procedure Poll (Reader : in ReaderT)
     with Refined_Global  => (Input  => (Clock.Now,
                                         ConfigData.State,
                                         Interfac.ReaderInput,
                                         Interfac.ReaderStatus),
                              In_Out => (AuditLog.FileState,
                                         AuditLog.State,
                                         ReaderStatus)),
          Refined_Depends => ((AuditLog.FileState,
                               AuditLog.State)     => (AuditLog.FileState,
                                                       AuditLog.State,
                                                       Clock.Now,
                                                       ConfigData.State,
                                                       Interfac.ReaderStatus,
                                                       Reader,
                                                       ReaderStatus),
                              ReaderStatus         =>+ (Interfac.ReaderInput,
                                                        Interfac.ReaderStatus,
                                                        Reader))
   is
      ResponseCode  : CommonTypes.Unsigned32T;
      RawNewState   : CommonTypes.Unsigned32T;
      NewState      : Interfac.ReaderStateT;

      StatusChangeTimeout : constant := 0;

      ------------------------------------------------------------------
      -- DisconnectToken
      --
      -- Description:
      --    Disconnects from the current token if there is one connected.
      --
      -- Implementation Notes:
      --    None.
      ------------------------------------------------------------------
      procedure DisconnectToken
        with Global  => (Input  => (Interfac.ReaderStatus,
                                    Reader,
                                    ReaderStatus)),
             Depends => (null => (Interfac.ReaderStatus,
                                  Reader,
                                  ReaderStatus))
      is
        UnusedResponseCode : CommonTypes.Unsigned32T;
      begin
         pragma Warnings (Off);
         if ReaderStatus(Reader).TokenConnected then
            Interfac.Disconnect
              (CardHandle   => ReaderStatus(Reader).TokenHandle,
               ResponseCode => UnusedResponseCode);
         end if;
         pragma Warnings (On);
      end DisconnectToken;

      ------------------------------------------------------------------
      -- MarkTokenBad
      --
      -- Description:
      --    Marks the current token as bad.
      --
      -- Implementation Notes:
      --    None.
      ------------------------------------------------------------------
      procedure MarkTokenBad
        with Global  => (Input  => (Interfac.ReaderStatus,
                                    Reader),
                         In_Out => ReaderStatus),
             Depends => (ReaderStatus =>+ Reader,
                         null         => Interfac.ReaderStatus)
      is
      begin
         DisconnectToken;
         ReaderStatus(Reader).TokenTry       := TokenTypes.BadToken;
         ReaderStatus(Reader).TokenID        := TokenTypes.TokenIDT'First;
         ReaderStatus(Reader).TokenHandle    := Interfac.NullHandle;
         ReaderStatus(Reader).TokenConnected := False;

      end MarkTokenBad;

      ------------------------------------------------------------------
      -- MarkTokenAbsent
      --
      -- Description:
      --    Marks the token as absent.
      --
      -- Implementation Notes:
      --    None.
      ------------------------------------------------------------------
      procedure MarkTokenAbsent
        with Global  => (Input  => (Interfac.ReaderStatus,
                                    Reader),
                         In_Out => ReaderStatus),
             Depends => (ReaderStatus =>+ Reader,
                         null         => Interfac.ReaderStatus)
      is
      begin
         DisconnectToken;
         ReaderStatus(Reader).TokenTry       := TokenTypes.NoToken;
         ReaderStatus(Reader).TokenID        := TokenTypes.TokenIDT'First;
         ReaderStatus(Reader).TokenHandle    := Interfac.NullHandle;
         ReaderStatus(Reader).TokenConnected := False;

      end MarkTokenAbsent;


      ------------------------------------------------------------------
      -- ProcessReaderStateChange
      --
      -- Description:
      --    Processes the detected change in reader state.
      --
      -- Implementation Notes:
      --    None.
      ------------------------------------------------------------------
      procedure ProcessReaderStateChange
        with Global  => (Input  => (Interfac.ReaderStatus,
                                    NewState,
                                    Reader),
                         In_Out => ReaderStatus),
             Depends => (ReaderStatus =>+ (Interfac.ReaderStatus,
                                           NewState,
                                           Reader))
      is
        TheCardHandle : Interfac.CardHandleT;
        ResponseCode  : CommonTypes.Unsigned32T;

        ------------------------------------------------------------------
        -- MarkTokenConnected
        --
        -- Description:
        --    Indicate that a token has become connected.
        --
        -- Implementation Notes:
        --    None.
        ------------------------------------------------------------------
        procedure MarkTokenConnected
          with Global  => (Input  => (Reader,
                                      TheCardHandle),
                           In_Out => ReaderStatus),
               Depends => (ReaderStatus =>+ (Reader,
                                             TheCardHandle))
        is
        begin
           ReaderStatus(Reader).TokenHandle    := TheCardHandle;
           ReaderStatus(Reader).TokenConnected := True;

        end MarkTokenConnected;

        -----------------------------------------------------------------
        -- begin ProcessReaderStateChange
        -----------------------------------------------------------------
      begin

         case NewState is
            when Interfac.Unaware..Interfac.Empty =>
               MarkTokenAbsent;

            when Interfac.CardPresent =>
               if not ReaderStatus(Reader).TokenConnected then
                  Interfac.Connect
                    (Reader       => ReaderStatus(Reader).Name,
                     CardHandle   => TheCardHandle,
                     ResponseCode => ResponseCode);

                  if ResponseCode = Interfac.ResponseCodeT'Pos
                    (Interfac.Success)
                  then
                     MarkTokenConnected;
                  else
                     MarkTokenBad;
                  end if;
               end if;

            when Interfac.Mute =>
               MarkTokenBad;

            when Interfac.InvalidReaderState =>
               MarkTokenAbsent;

         end case;
      end ProcessReaderStateChange;

      ------------------------------------------------------------------
      -- CheckCardState
      --
      -- Description:
      --    Checks the card state where the reader claims there is
      --    a card present.
      --
      -- Implementation Notes:
      --    None.
      ------------------------------------------------------------------
      procedure CheckCardState
        with Global  => (Input  => (Interfac.ReaderInput,
                                    Interfac.ReaderStatus,
                                    Reader),
                         In_Out => ReaderStatus),
             Depends => (ReaderStatus =>+ (Interfac.ReaderInput,
                                           Interfac.ReaderStatus,
                                           Reader))
      is
        RawCardState : CommonTypes.Unsigned32T;
        CardState    : Interfac.CardStateT;
        ResponseCode : CommonTypes.Unsigned32T;
        TheATR       : TokenTypes.TokenIDT;

        ------------------------------------------------------------------
        -- MarkTokenGood
        --
        -- Description:
        --    Indicate that a token has extablished communications
        --    so can be assumed good.
        --
        -- Implementation Notes:
        --    None.
        ------------------------------------------------------------------
        procedure MarkTokenGood
          with Global  => (Input  => (Reader,
                                      TheATR),
                           In_Out => ReaderStatus),
               Depends => (ReaderStatus =>+ (Reader,
                                             TheATR))
        is
        begin
           ReaderStatus(Reader).TokenTry := TokenTypes.GoodToken;
           ReaderStatus(Reader).TokenID  := TheATR;
        end MarkTokenGood;

        -----------------------------------------------------------------
        -- begin CheckCardState
        -----------------------------------------------------------------
      begin
         Interfac.Status
           (CardHandle   => ReaderStatus(Reader).TokenHandle,
            CState       => RawCardState,
            ATR          => TheATR,
            ResponseCode => ResponseCode);

         if ResponseCode = Interfac.ResponseCodeT'Pos(Interfac.Success) then

            CardState := GetCardState(RawCardState);

            case CardState is
               when Interfac.Absent =>
                  MarkTokenAbsent;
               when Interfac.Present..Interfac.Powered =>
                  null;
                  -- keep waiting
               when Interfac.Negotiable..Interfac.Specific =>
                  MarkTokenGood;
               when Interfac.InvalidCardState =>
                  MarkTokenBad;
            end case;

         else

            MarkTokenBad;
         end if;

      end CheckCardState;

      ------------------------------------------------------------------
      -- SetCurrentStatus
      --
      -- Description:
      --    Sets the Reader Status to the supplied value.
      --
      -- Implementation Notes:
      --    Presented as a subroutine to aid VCG.
      ------------------------------------------------------------------
      procedure SetCurrentStatus (TheStatus : in Interfac.ValidReaderStateT)
        with Global  => (Input  => Reader,
                         In_Out => ReaderStatus),
             Depends => (ReaderStatus =>+ (Reader,
                                           TheStatus))
      is
      begin
         ReaderStatus(Reader).CurrentStatus := TheStatus;
      end SetCurrentStatus;

      ------------------------------------------------------------------
      -- SetLastFault
      --
      -- Description:
      --    Sets the Reader's last fault to the ResponseCode.
      --
      -- Implementation Notes:
      --    Presented as a subroutine to aid VCG.
      ------------------------------------------------------------------
     procedure SetLastFault
       with Global  => (Input  => (Reader,
                                   ResponseCode),
                        In_Out => ReaderStatus),
            Depends => (ReaderStatus =>+ (Reader,
                                          ResponseCode))
     is
     begin
        ReaderStatus(Reader).LastFault := ResponseCode;
     end SetLastFault;

   -----------------------------------------------------------------
   -- begin Poll
   -----------------------------------------------------------------
   begin

      Interfac.GetStatusChange
        (Timeout      => StatusChangeTimeout,
         Reader       => ReaderStatus(Reader).Name,
         CurrentState => ReaderStatus(Reader).CurrentStatus,
         NewState     => RawNewState,
         ResponseCode => ResponseCode);

      if ResponseCode = Interfac.ResponseCodeT'Pos(Interfac.Success) then

         NewState := GetReaderState(RawNewState);
         ProcessReaderStateChange;
         if NewState in Interfac.ValidReaderStateT then
            SetCurrentStatus(TheStatus => NewState);
         else
            SetCurrentStatus(TheStatus => Interfac.Unaware);
         end if;

      elsif ResponseCode = Interfac.ResponseCodeT'Pos(Interfac.Timedout)then

         -- no change to the state.
         null;

      else

         MarkTokenAbsent;
         SetCurrentStatus(TheStatus => Interfac.Unaware);

         -- only log the fault the first time it happens:
         if ReaderStatus(Reader).LastFault /= ResponseCode then

            SetLastFault;

            AuditLog.AddElementToLog
              (ElementID   => AuditTypes.SystemFault,
               Severity    => AuditTypes.Warning,
               User        => AuditTypes.NoUser,
               Description =>
                 MakeDescription("Token Reader status change failure : ",
                                 ResponseCode));

         end if;

      end if;

      if ReaderStatus(Reader).CurrentStatus = Interfac.CardPresent and
        ReaderStatus(Reader).TokenConnected
      then
         CheckCardState;
      end if;

   end Poll;

   ------------------------------------------------------------------
   -- TheTokenTry
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   function TheTokenTry (Reader : ReaderT) return TokenTypes.TryT is
     (ReaderStatus(Reader).TokenTry)
     with Refined_Global => ReaderStatus;

   ------------------------------------------------------------------
   -- TheTokenPresence
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   function TheTokenPresence (Reader :  ReaderT) return CommonTypes.PresenceT
   is
     (if ReaderStatus(Reader).TokenTry = TokenTypes.NoToken then
         CommonTypes.Absent
      else
         CommonTypes.Present)
     with Refined_Global => ReaderStatus;

   ------------------------------------------------------------------
   -- TheTokenID
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   function TheTokenID (Reader : ReaderT) return TokenTypes.TokenIDT is
     (ReaderStatus(Reader).TokenID)
     with Refined_Global => ReaderStatus;

   ------------------------------------------------------------------
   -- GetCertificate
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure GetCertificate (Reader   : in     ReaderT;
                             CertType : in     CertTypes.CertificateT;
                             RawCert  :    out CertTypes.RawCertificateT;
                             Found    :    out Boolean)
     with Refined_Global  => (Input  => (Interfac.ReaderInput,
                                         Interfac.ReaderStatus,
                                         ReaderStatus)),
          Refined_Depends => (Found   => (CertType,
                                          Interfac.ReaderStatus,
                                          Reader,
                                          ReaderStatus),
                              RawCert => (CertType,
                                          Interfac.ReaderInput,
                                          Interfac.ReaderStatus,
                                          Reader,
                                          ReaderStatus))
   is
      StatusOK     : Boolean;
      Exists       : Boolean := True;
      ResponseCode : CommonTypes.Unsigned32T;
   begin

      RawCert := CertTypes.NullRawCertificate;

      if ReaderStatus(Reader).TokenTry = TokenTypes.GoodToken then
         case CertType is
            when CertTypes.IDCert =>
               Interfac.GetIDCert
                 (CardHandle   => ReaderStatus(Reader).TokenHandle,
                  RawIDCert    => RawCert,
                  StatusOK     => StatusOK,
                  ResponseCode => ResponseCode);
            when CertTypes.AuthCert =>
               Interfac.GetAuthCert
                 (CardHandle   => ReaderStatus(Reader).TokenHandle,
                  RawAuthCert  => RawCert,
                  StatusOK     => StatusOK,
                  Exists       => Exists,
                  ResponseCode => ResponseCode);
            when CertTypes.PrivCert =>
               Interfac.GetPrivCert
                 (CardHandle   => ReaderStatus(Reader).TokenHandle,
                  RawPrivCert  => RawCert,
                  StatusOK     => StatusOK,
                  ResponseCode => ResponseCode);
            when CertTypes.IandACert =>
               Interfac.GetIACert
                 (CardHandle   => ReaderStatus(Reader).TokenHandle,
                  RawIACert    => RawCert,
                  StatusOK     => StatusOK,
                  ResponseCode => ResponseCode);
         end case;

         Found := StatusOK and Exists and
              (ResponseCode = Interfac.ResponseCodeT'Pos(Interfac.Success));

      else
         Found := False;
      end if;

   end GetCertificate;

   ------------------------------------------------------------------
   -- WriteAuthCertificate
   --
   -- Implementation Notes:
   --     None.
   ------------------------------------------------------------------
   procedure WriteAuthCertificate
     (RawCert : in     CertTypes.RawCertificateT;
      Success :    out Boolean)
     with Refined_Global  => (Input  => (Interfac.ReaderStatus,
                                         ReaderStatus),
                              Output => Interfac.ReaderOutput),
          Refined_Depends => (Interfac.ReaderOutput => (Interfac.ReaderStatus,
                                                        RawCert,
                                                        ReaderStatus),
                              Success               => (Interfac.ReaderStatus,
                                                        ReaderStatus))

   is
      StatusOK     : Boolean;
      ResponseCode : CommonTypes.Unsigned32T;
   begin
        Interfac.UpdateAuthCert
         (CardHandle   => ReaderStatus(User).TokenHandle,
          RawAuthCert  => RawCert,
          StatusOK     => StatusOK,
          ResponseCode => ResponseCode);

        Success := StatusOK and
              (ResponseCode = Interfac.ResponseCodeT'Pos(Interfac.Success));

   end WriteAuthCertificate;

end TokenReader;
