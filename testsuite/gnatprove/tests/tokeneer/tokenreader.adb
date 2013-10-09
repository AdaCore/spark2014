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

with BasicTypes;
use type BasicTypes.Unsigned32T;

package body TokenReader
--# own State is ReaderStatus &
--#     Status is in TokenReader.Interfac.ReaderStatus &
--#     Input is in TokenReader.Interfac.ReaderInput &
--#     Output is out TokenReader.Interfac.ReaderOutput;
is pragma SPARK_Mode (On);

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
      LastFault      : BasicTypes.Unsigned32T;
   end record;

   NoReaderInfo : constant ReaderInfoT :=
     ReaderInfoT'(Name           => "UNKNOWN ",
                  TokenTry       => TokenTypes.NoToken,
                  TokenID        => TokenTypes.TokenIDT'First,
                  TokenConnected => False,
                  TokenHandle    => Interfac.NullHandle,
                  CurrentStatus  => Interfac.Unaware,
                  LastFault      => BasicTypes.Unsigned32T'First);

   type ReaderInfoArrayT is array (ReaderT) of ReaderInfoT;

   NoReaders : constant ReaderInfoArrayT
     := ReaderInfoArrayT'(others => NoReaderInfo);

   type ReaderNameArrayT is array (ReaderT) of Interfac.ReaderNameT;

   ExpectedReaderNames : constant ReaderNameArrayT
     := ReaderNameArrayT'(User  => "EXTREAD ",
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
   function GetResponseCode (ResponseCode : BasicTypes.Unsigned32T) return
     Interfac.ResponseCodeT
   is
      Result : Interfac.ResponseCodeT;
   begin
      if ResponseCode >=
        Interfac.ResponseCodeT'Pos(Interfac.ResponseCodeT'First)
        and ResponseCode <=
        Interfac.ResponseCodeT'Pos(Interfac.ResponseCodeT'Last) then
         Result := Interfac.ResponseCodeT'Val(ResponseCode);
      else
         Result := Interfac.InvalidResponseCode;
      end if;
      return Result;
   end GetResponseCode;

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
   function GetReaderState (ReaderState : BasicTypes.Unsigned32T) return
     Interfac.ReaderStateT
   is
      Result : Interfac.ReaderStateT;
   begin
      if ReaderState >=
        Interfac.ReaderStateT'Pos(Interfac.ReaderStateT'First)
        and ReaderState <=
        Interfac.ReaderStateT'Pos(Interfac.ReaderStateT'Last) then
         Result := Interfac.ReaderStateT'Val(ReaderState);
      else
         Result := Interfac.InvalidReaderState;
      end if;
      return Result;
   end GetReaderState;

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
   function GetCardState (CardState : BasicTypes.Unsigned32T) return
     Interfac.CardStateT
   is
      Result : Interfac.CardStateT;
   begin
      if CardState >=
        Interfac.CardStateT'Pos(Interfac.CardStateT'First)
        and CardState <=
        Interfac.CardStateT'Pos(Interfac.CardStateT'Last) then
         Result := Interfac.CardStateT'Val(CardState);
      else
         Result := Interfac.InvalidCardState;
      end if;
      return Result;
   end GetCardState;

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
     (Text         : String;
      ResponseCode : BasicTypes.Unsigned32T) return AuditTypes.DescriptionT;
   function MakeDescription
     (Text         : String;
      ResponseCode : BasicTypes.Unsigned32T) return AuditTypes.DescriptionT
   is
      pragma SPARK_Mode (Off);  --  concatenation
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
      --# global in     Text;
      --#        in     TheCodeName;
      --#        in     ResponseCode;
      --#        in out Result;
      --# derives Result from *,
      --#                     Text,
      --#                     TheCodeName,
      --#                     ResponseCode;
      is
         --# hide SetResultString;

         FullString : String := Text & ": "
           & Interfac.ResponseCodeT'Image(TheCodeName) & " ( "
           & BasicTypes.Unsigned32T'Image(ResponseCode) & " )";
      begin

         -- if the Full string is shorter then use it all otherwise
         -- truncate it.
         if FullString'Last <= AuditTypes.DescriptionI'Last then
            Result (1.. FullString'Last) := FullString;
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
   --# global in     Interfac.ReaderStatus;
   --#        in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out AuditLog.FileState;
   --#        in out AuditLog.State;
   --#           out ReaderStatus;
   --# derives AuditLog.FileState,
   --#         AuditLog.State     from AuditLog.FileState,
   --#                                 AuditLog.State,
   --#                                 Interfac.ReaderStatus,
   --#                                 Clock.Now,
   --#                                 ConfigData.State &
   --#         ReaderStatus       from Interfac.ReaderStatus;
   is
      NumberReaders : BasicTypes.Unsigned32T;
      ResponseCode  : BasicTypes.Unsigned32T;
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
      --# global in out ReaderStatus;
      --# derives ReaderStatus from *,
      --#                           TheReader,
      --#                           TheName;
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
      --# global out ReaderStatus;
      --# derives ReaderStatus from ;
      is
      begin
         ReaderStatus := NoReaders;
      end ClearReaders;

      -----------------------------------------------------------------
      -- begin Init
      ----------------------------------------------------------------
   begin

      ClearReaders;

      -- We are looking for 2 readers.
      NumberReaders := 2;
      Interfac.ListReaders(List         => Readers,
                            Number       => NumberReaders,
                            ResponseCode => ResponseCode);

      if ResponseCode = Interfac.ResponseCodeT'Pos(Interfac.Success) then

         if NumberReaders >=
           BasicTypes.Unsigned32T(Interfac.ReaderArrayI'First) and
           NumberReaders <=
           BasicTypes.Unsigned32T(Interfac.ReaderArrayI'Last) then
            for I in Interfac.ReaderArrayI
              range 1 .. Interfac.ReaderArrayI(NumberReaders) loop
               --# assert I in Interfac.ReaderArrayI and
               --#        I <= Interfac.ReaderArrayI(NumberReaders) and
               --#        Interfac.ReaderArrayI(NumberReaders) >=
               --#           Interfac.ReaderArrayI'First and
               --#        Interfac.ReaderArrayI(NumberReaders) <=
               --#           Interfac.ReaderArrayI'Last and
               --#        ReaderStatus in ReaderInfoArrayT and
               --#        NumberReaders = NumberReaders% and
               --#        ( for all L in Interfac.ReaderNameI =>
               --#            (for all K in ReaderT =>
               --#         (ReaderStatus(K).Name(L) in Character))) and
               --#        (for all K in ReaderT =>
               --#         (ReaderStatus(K).TokenTry in TokenTypes.TryT)) and
               --#        (for all K in ReaderT =>
               --#         (ReaderStatus(K).TokenID in TokenTypes.TokenIDT))  and
               --#        (for all K in ReaderT =>
               --#         (ReaderStatus(K).TokenHandle
               --#                    in Interfac.CardHandleT)) and
               --#        (for all K in ReaderT =>
               --#         (ReaderStatus(K).CurrentStatus
               --#                    in Interfac.ValidReaderStateT)) and
               --#        (for all K in ReaderT =>
               --#         (ReaderStatus(K).LastFault in BasicTypes.Unsigned32T));
               for R in ReaderT loop
                  --# assert I in Interfac.ReaderArrayI and
                  --#        I <= Interfac.ReaderArrayI(NumberReaders) and
                  --#        Interfac.ReaderArrayI(NumberReaders) >=
                  --#           Interfac.ReaderArrayI'First and
                  --#        Interfac.ReaderArrayI(NumberReaders) <=
                  --#           Interfac.ReaderArrayI'Last and
                  --#        R in ReaderT and
                  --#        NumberReaders = NumberReaders% and
                  --#       ( for all L in Interfac.ReaderNameI =>
                  --#            (for all K in ReaderT =>
                  --#         (ReaderStatus(K).Name(L) in Character))) and
                  --#        (for all K in ReaderT =>
                  --#         (ReaderStatus(K).TokenTry in TokenTypes.TryT)) and
                  --#        (for all K in ReaderT =>
                  --#         (ReaderStatus(K).TokenID
                  --#             in TokenTypes.TokenIDT))  and
                  --#        (for all K in ReaderT =>
                  --#         (ReaderStatus(K).TokenHandle
                  --#             in Interfac.CardHandleT)) and
                  --#        (for all K in ReaderT =>
                  --#         (ReaderStatus(K).CurrentStatus
                  --#             in Interfac.ValidReaderStateT)) and
                  --#        (for all K in ReaderT =>
                  --#         (ReaderStatus(K).LastFault in BasicTypes.Unsigned32T));

                  if ExpectedReaderNames(R) = Readers(I) then
                     SetReaderName(TheReader => R,
                                   TheName   => Readers(I));
                     exit;
                  end if;
               end loop;
            end loop;

              if ReaderStatus(User).Name /= ExpectedReaderNames(User) then

                 AuditLog.AddElementToLog
                   ( ElementID   => AuditTypes.SystemFault,
                     Severity    => AuditTypes.Warning,
                     User        => AuditTypes.NoUser,
                     Description => "Token Reader initialisation failure : " &
                     "External token reader not found");

              end if;

              if ReaderStatus(Admin).Name /= ExpectedReaderNames(Admin) then

                 AuditLog.AddElementToLog
                   ( ElementID   => AuditTypes.SystemFault,
                     Severity    => AuditTypes.Warning,
                     User        => AuditTypes.NoUser,
                     Description => "Token Reader initialisation failure : " &
                     "Internal token reader not found");

              end if;

         else

            AuditLog.AddElementToLog
              ( ElementID   => AuditTypes.SystemFault,
                Severity    => AuditTypes.Warning,
                User        => AuditTypes.NoUser,
                Description => "Token Reader initialisation failure : "
                & "Invalid Number of Token Readers found");

         end if;

      else

         AuditLog.AddElementToLog
           ( ElementID   => AuditTypes.SystemFault,
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

   procedure Poll ( Reader : in ReaderT)
   --# global in     Interfac.ReaderStatus;
   --#        in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in     Interfac.ReaderInput;
   --#        in out AuditLog.FileState;
   --#        in out AuditLog.State;
   --#        in out ReaderStatus;
   --# derives AuditLog.FileState,
   --#         AuditLog.State     from AuditLog.FileState,
   --#                                 AuditLog.State,
   --#                                 ReaderStatus,
   --#                                 Interfac.ReaderStatus,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 Reader &
   --#         ReaderStatus       from *,
   --#                                 Interfac.ReaderStatus,
   --#                                 Interfac.ReaderInput,
   --#                                 Reader;
   is
      ResponseCode  : BasicTypes.Unsigned32T;
      RawNewState   : BasicTypes.Unsigned32T;
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
      --# global in ReaderStatus;
      --#        in Interfac.ReaderStatus;
      --#        in Reader;
      --# derives null from ReaderStatus,
      --#                   Interfac.ReaderStatus,
      --#                   Reader;
      is
        UnusedResponseCode : BasicTypes.Unsigned32T;
      begin
         --# accept F, 10, UnusedResponseCode, "Ineffective assignment expected here" &
         --#        F, 33, UnusedResponseCode, "Ineffective assignment expected here";
         if ReaderStatus(Reader).TokenConnected then
            Interfac.Disconnect
              (CardHandle   => ReaderStatus(Reader).TokenHandle,
               ResponseCode => UnusedResponseCode);
         end if;
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
      --# global in     Interfac.ReaderStatus;
      --#        in     Reader;
      --#        in out ReaderStatus;
      --# derives ReaderStatus from *,
      --#                           Reader &
      --#         null         from Interfac.ReaderStatus;
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
      --# global in     Interfac.ReaderStatus;
      --#        in     Reader;
      --#        in out ReaderStatus;
      --# derives ReaderStatus from *,
      --#                           Reader &
      --#         null         from Interfac.ReaderStatus;
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
      --# global in     Interfac.ReaderStatus;
      --#        in     Reader;
      --#        in     NewState;
      --#        in out ReaderStatus;
      --# derives ReaderStatus from *,
      --#                           Interfac.ReaderStatus,
      --#                           Reader,
      --#                           NewState;
      is
        TheCardHandle : Interfac.CardHandleT;
        ResponseCode  : BasicTypes.Unsigned32T;

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
          --# global in     Reader;
          --#        in     TheCardHandle;
          --#        in out ReaderStatus;
          --# derives ReaderStatus from *,
          --#                           Reader,
          --#                           TheCardHandle;
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
            when Interfac.Unaware .. Interfac.Empty =>
               MarkTokenAbsent;

            when Interfac.CardPresent =>
               if not ReaderStatus(Reader).TokenConnected then
                  Interfac.Connect
                    (Reader       => ReaderStatus(Reader).Name,
                     CardHandle   => TheCardHandle,
                     ResponseCode => ResponseCode);

                    if ResponseCode = Interfac.ResponseCodeT'Pos(Interfac.Success) then
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
      --# global in     Interfac.ReaderStatus;
      --#        in     Interfac.ReaderInput;
      --#        in     Reader;
      --#        in out ReaderStatus;
      --# derives ReaderStatus from *,
      --#                           Interfac.ReaderStatus,
      --#                           Interfac.ReaderInput,
      --#                           Reader;
      is
        RawCardState        : BasicTypes.Unsigned32T;
        CardState           : Interfac.CardStateT;
        ResponseCode        : BasicTypes.Unsigned32T;
        TheATR              : TokenTypes.TokenIDT;

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
          --# global in     Reader;
          --#        in     TheATR;
          --#        in out ReaderStatus;
          --# derives ReaderStatus from *,
          --#                           Reader,
          --#                           TheATR;
        is
        begin
           ReaderStatus(Reader).TokenTry       := TokenTypes.GoodToken;
           ReaderStatus(Reader).TokenID        := TheATR;

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
               when Interfac.Present  .. Interfac.Powered =>
                  null;
                  -- keep waiting
               when Interfac.Negotiable .. Interfac.Specific =>
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
        --# global in     Reader;
        --#        in out ReaderStatus;
        --# derives ReaderStatus from *,
        --#                           Reader,
        --#                           TheStatus;
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
     --# global in     ResponseCode;
     --#        in     Reader;
     --#        in out ReaderStatus;
     --# derives ReaderStatus from *,
     --#                           ResponseCode,
     --#                           Reader;
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
              ( ElementID   => AuditTypes.SystemFault,
                Severity    => AuditTypes.Warning,
                User        => AuditTypes.NoUser,
                Description =>
                  MakeDescription("Token Reader status change failure : ",
                                  ResponseCode));

         end if;

      end if;

      if ReaderStatus(Reader).CurrentStatus = Interfac.CardPresent and
        ReaderStatus(Reader).TokenConnected then
         CheckCardState;
      end if;

   end Poll;

   ------------------------------------------------------------------
   -- TheTokenTry
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------

   function TheTokenTry (Reader : ReaderT) return  TokenTypes.TryT
   --# global ReaderStatus;
   is
   begin
      return ReaderStatus(Reader).TokenTry;
   end TheTokenTry;

   ------------------------------------------------------------------
   -- TheTokenPresence
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------

   function TheTokenPresence (Reader  :  ReaderT) return BasicTypes.PresenceT
   --# global ReaderStatus;
   is
      Result : BasicTypes.PresenceT;
   begin
      if ReaderStatus(Reader).TokenTry = TokenTypes.NoToken then
         Result := BasicTypes.Absent;
      else
         Result := BasicTypes.Present;
      end if;
      return Result;
   end TheTokenPresence;

   ------------------------------------------------------------------
   -- TheTokenID
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------

   function TheTokenID (Reader : ReaderT) return  TokenTypes.TokenIDT
   --# global ReaderStatus;
   is
   begin
      return ReaderStatus(Reader).TokenID;
   end TheTokenID;

   ------------------------------------------------------------------
   -- GetCertificate
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------

   procedure GetCertificate (Reader    : in     ReaderT;
                             CertType  : in     CertTypes.CertificateT;
                             RawCert   :    out CertTypes.RawCertificateT;
                             Found     :    out Boolean)
   --# global in ReaderStatus;
   --#        in Interfac.ReaderStatus;
   --#        in Interfac.ReaderInput;
   --# derives Found   from ReaderStatus,
   --#                      Interfac.ReaderStatus,
   --#                      Reader,
   --#                      CertType &
   --#         RawCert from ReaderStatus,
   --#                      Interfac.ReaderStatus,
   --#                      Interfac.ReaderInput,
   --#                      Reader,
   --#                      CertType;
   is
      StatusOK     : Boolean;
      Exists       : Boolean := True;
      ResponseCode : BasicTypes.Unsigned32T;
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
                  RawIACert  => RawCert,
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
     (RawCert   : in     CertTypes.RawCertificateT;
      Success   :    out Boolean)
   --# global in     ReaderStatus;
   --#        in     Interfac.ReaderStatus;
   --#           out Interfac.ReaderOutput;
   --# derives Interfac.ReaderOutput from ReaderStatus,
   --#                                     Interfac.ReaderStatus,
   --#                                     RawCert &
   --#         Success                from ReaderStatus,
   --#                                     Interfac.ReaderStatus;

   is
      StatusOK     : Boolean;
      ResponseCode : BasicTypes.Unsigned32T;
   begin
        Interfac.UpdateAuthCert
         (CardHandle   => ReaderStatus(User).TokenHandle ,
          RawAuthCert  => RawCert,
          StatusOK     => StatusOK,
          ResponseCode => ResponseCode);

        Success := StatusOK and
              (ResponseCode = Interfac.ResponseCodeT'Pos(Interfac.Success));

   end WriteAuthCertificate;

end TokenReader;
