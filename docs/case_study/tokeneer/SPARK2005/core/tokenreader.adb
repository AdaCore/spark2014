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
with TokenReader.Interface;
use type TokenReader.Interface.ReaderStateT;

with AuditTypes;
with AuditLog;

with TokenTypes;
use type TokenTypes.TryT;

with BasicTypes;
use type BasicTypes.Unsigned32T;

package body TokenReader
--# own State is ReaderStatus &
--#     Status is in TokenReader.Interface.ReaderStatus &
--#     Input is in TokenReader.Interface.ReaderInput &
--#     Output is out TokenReader.Interface.ReaderOutput;
is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   type ReaderInfoT is record
      Name           : Interface.ReaderNameT;
      TokenTry       : TokenTypes.TryT;
      TokenID        : TokenTypes.TokenIDT;
      TokenConnected : Boolean;
      TokenHandle    : Interface.CardHandleT;
      CurrentStatus  : Interface.ValidReaderStateT;
      LastFault      : BasicTypes.Unsigned32T;
   end record;

   NoReaderInfo : constant ReaderInfoT :=
     ReaderInfoT'(Name           => "UNKNOWN ",
                  TokenTry       => TokenTypes.NoToken,
                  TokenID        => TokenTypes.TokenIDT'First,
                  TokenConnected => False,
                  TokenHandle    => Interface.NullHandle,
                  CurrentStatus  => Interface.Unaware,
                  LastFault      => BasicTypes.Unsigned32T'First);

   type ReaderInfoArrayT is array (ReaderT) of ReaderInfoT;

   NoReaders : constant ReaderInfoArrayT
     := ReaderInfoArrayT'(others => NoReaderInfo);

   type ReaderNameArrayT is array (ReaderT) of Interface.ReaderNameT;

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
     Interface.ResponseCodeT
   is
      Result : Interface.ResponseCodeT;
   begin
      if ResponseCode >=
        Interface.ResponseCodeT'Pos(Interface.ResponseCodeT'First)
        and ResponseCode <=
        Interface.ResponseCodeT'Pos(Interface.ResponseCodeT'Last) then
         Result := Interface.ResponseCodeT'Val(ResponseCode);
      else
         Result := Interface.InvalidResponseCode;
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
     Interface.ReaderStateT
   is
      Result : Interface.ReaderStateT;
   begin
      if ReaderState >=
        Interface.ReaderStateT'Pos(Interface.ReaderStateT'First)
        and ReaderState <=
        Interface.ReaderStateT'Pos(Interface.ReaderStateT'Last) then
         Result := Interface.ReaderStateT'Val(ReaderState);
      else
         Result := Interface.InvalidReaderState;
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
     Interface.CardStateT
   is
      Result : Interface.CardStateT;
   begin
      if CardState >=
        Interface.CardStateT'Pos(Interface.CardStateT'First)
        and CardState <=
        Interface.CardStateT'Pos(Interface.CardStateT'Last) then
         Result := Interface.CardStateT'Val(CardState);
      else
         Result := Interface.InvalidCardState;
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
      ResponseCode : BasicTypes.Unsigned32T) return AuditTypes.DescriptionT
   is
      Result : AuditTypes.DescriptionT := AuditTypes.NoDescription;
      TheCodeName : Interface.ResponseCodeT;

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
           & Interface.ResponseCodeT'Image(TheCodeName) & " ( "
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
   --# global in     Interface.ReaderStatus;
   --#        in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out AuditLog.FileState;
   --#        in out AuditLog.State;
   --#           out ReaderStatus;
   --# derives AuditLog.FileState,
   --#         AuditLog.State     from AuditLog.FileState,
   --#                                 AuditLog.State,
   --#                                 Interface.ReaderStatus,
   --#                                 Clock.Now,
   --#                                 ConfigData.State &
   --#         ReaderStatus       from Interface.ReaderStatus;
   is
      NumberReaders : BasicTypes.Unsigned32T;
      ResponseCode  : BasicTypes.Unsigned32T;
      Readers       : Interface.ReaderNameArrayT;

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
                               TheName   : in Interface.ReaderNameT)
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
      Interface.ListReaders(List         => Readers,
                            Number       => NumberReaders,
                            ResponseCode => ResponseCode);

      if ResponseCode = Interface.ResponseCodeT'Pos(Interface.Success) then

         if NumberReaders >=
           BasicTypes.Unsigned32T(Interface.ReaderArrayI'First) and
           NumberReaders <=
           BasicTypes.Unsigned32T(Interface.ReaderArrayI'Last) then
            for I in Interface.ReaderArrayI
              range 1 .. Interface.ReaderArrayI(NumberReaders) loop
               --# assert I in Interface.ReaderArrayI and
               --#        I <= Interface.ReaderArrayI(NumberReaders) and
               --#        Interface.ReaderArrayI(NumberReaders) >=
               --#           Interface.ReaderArrayI'First and
               --#        Interface.ReaderArrayI(NumberReaders) <=
               --#           Interface.ReaderArrayI'Last and
               --#        ReaderStatus in ReaderInfoArrayT and
               --#        NumberReaders = NumberReaders% and
               --#        ( for all L in Interface.ReaderNameI =>
               --#            (for all K in ReaderT =>
               --#         (ReaderStatus(K).Name(L) in Character))) and
               --#        (for all K in ReaderT =>
               --#         (ReaderStatus(K).TokenTry in TokenTypes.TryT)) and
               --#        (for all K in ReaderT =>
               --#         (ReaderStatus(K).TokenID in TokenTypes.TokenIDT))  and
               --#        (for all K in ReaderT =>
               --#         (ReaderStatus(K).TokenHandle
               --#                    in Interface.CardHandleT)) and
               --#        (for all K in ReaderT =>
               --#         (ReaderStatus(K).CurrentStatus
               --#                    in Interface.ValidReaderStateT)) and
               --#        (for all K in ReaderT =>
               --#         (ReaderStatus(K).LastFault in BasicTypes.Unsigned32T));
               for R in ReaderT loop
                  --# assert I in Interface.ReaderArrayI and
                  --#        I <= Interface.ReaderArrayI(NumberReaders) and
                  --#        Interface.ReaderArrayI(NumberReaders) >=
                  --#           Interface.ReaderArrayI'First and
                  --#        Interface.ReaderArrayI(NumberReaders) <=
                  --#           Interface.ReaderArrayI'Last and
                  --#        R in ReaderT and
                  --#        NumberReaders = NumberReaders% and
                  --#       ( for all L in Interface.ReaderNameI =>
                  --#            (for all K in ReaderT =>
                  --#         (ReaderStatus(K).Name(L) in Character))) and
                  --#        (for all K in ReaderT =>
                  --#         (ReaderStatus(K).TokenTry in TokenTypes.TryT)) and
                  --#        (for all K in ReaderT =>
                  --#         (ReaderStatus(K).TokenID
                  --#             in TokenTypes.TokenIDT))  and
                  --#        (for all K in ReaderT =>
                  --#         (ReaderStatus(K).TokenHandle
                  --#             in Interface.CardHandleT)) and
                  --#        (for all K in ReaderT =>
                  --#         (ReaderStatus(K).CurrentStatus
                  --#             in Interface.ValidReaderStateT)) and
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
   --# global in     Interface.ReaderStatus;
   --#        in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in     Interface.ReaderInput;
   --#        in out AuditLog.FileState;
   --#        in out AuditLog.State;
   --#        in out ReaderStatus;
   --# derives AuditLog.FileState,
   --#         AuditLog.State     from AuditLog.FileState,
   --#                                 AuditLog.State,
   --#                                 ReaderStatus,
   --#                                 Interface.ReaderStatus,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 Reader &
   --#         ReaderStatus       from *,
   --#                                 Interface.ReaderStatus,
   --#                                 Interface.ReaderInput,
   --#                                 Reader;
   is
      ResponseCode  : BasicTypes.Unsigned32T;
      RawNewState   : BasicTypes.Unsigned32T;
      NewState      : Interface.ReaderStateT;

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
      --#        in Interface.ReaderStatus;
      --#        in Reader;
      --# derives null from ReaderStatus,
      --#                   Interface.ReaderStatus,
      --#                   Reader;
      is
        UnusedResponseCode : BasicTypes.Unsigned32T;
      begin
         --# accept F, 10, UnusedResponseCode, "Ineffective assignment expected here" &
         --#        F, 33, UnusedResponseCode, "Ineffective assignment expected here";
         if ReaderStatus(Reader).TokenConnected then
            Interface.Disconnect
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
      --# global in     Interface.ReaderStatus;
      --#        in     Reader;
      --#        in out ReaderStatus;
      --# derives ReaderStatus from *,
      --#                           Reader &
      --#         null         from Interface.ReaderStatus;
      is
      begin
         DisconnectToken;
         ReaderStatus(Reader).TokenTry       := TokenTypes.BadToken;
         ReaderStatus(Reader).TokenID        := TokenTypes.TokenIDT'First;
         ReaderStatus(Reader).TokenHandle    := Interface.NullHandle;
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
      --# global in     Interface.ReaderStatus;
      --#        in     Reader;
      --#        in out ReaderStatus;
      --# derives ReaderStatus from *,
      --#                           Reader &
      --#         null         from Interface.ReaderStatus;
      is
      begin
         DisconnectToken;
         ReaderStatus(Reader).TokenTry       := TokenTypes.NoToken;
         ReaderStatus(Reader).TokenID        := TokenTypes.TokenIDT'First;
         ReaderStatus(Reader).TokenHandle    := Interface.NullHandle;
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
      --# global in     Interface.ReaderStatus;
      --#        in     Reader;
      --#        in     NewState;
      --#        in out ReaderStatus;
      --# derives ReaderStatus from *,
      --#                           Interface.ReaderStatus,
      --#                           Reader,
      --#                           NewState;
      is
        TheCardHandle : Interface.CardHandleT;
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
            when Interface.Unaware .. Interface.Empty =>
               MarkTokenAbsent;

            when Interface.CardPresent =>
               if not ReaderStatus(Reader).TokenConnected then
                  Interface.Connect
                    (Reader       => ReaderStatus(Reader).Name,
                     CardHandle   => TheCardHandle,
                     ResponseCode => ResponseCode);

                    if ResponseCode = Interface.ResponseCodeT'Pos(Interface.Success) then
                       MarkTokenConnected;
                    else
                       MarkTokenBad;
                    end if;
               end if;

            when Interface.Mute =>
               MarkTokenBad;

            when Interface.InvalidReaderState =>
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
      --# global in     Interface.ReaderStatus;
      --#        in     Interface.ReaderInput;
      --#        in     Reader;
      --#        in out ReaderStatus;
      --# derives ReaderStatus from *,
      --#                           Interface.ReaderStatus,
      --#                           Interface.ReaderInput,
      --#                           Reader;
      is
        RawCardState        : BasicTypes.Unsigned32T;
        CardState           : Interface.CardStateT;
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
         Interface.Status
           (CardHandle   => ReaderStatus(Reader).TokenHandle,
            CState       => RawCardState,
            ATR          => TheATR,
            ResponseCode => ResponseCode);


         if ResponseCode = Interface.ResponseCodeT'Pos(Interface.Success) then

            CardState := GetCardState(RawCardState);

            case CardState is
               when Interface.Absent =>
                  MarkTokenAbsent;
               when Interface.Present  .. Interface.Powered =>
                  null;
                  -- keep waiting
               when Interface.Negotiable .. Interface.Specific =>
                  MarkTokenGood;

               when Interface.InvalidCardState =>
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
      procedure SetCurrentStatus (TheStatus : in Interface.ValidReaderStateT)
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

      Interface.GetStatusChange
        (Timeout      => StatusChangeTimeout,
         Reader       => ReaderStatus(Reader).Name,
         CurrentState => ReaderStatus(Reader).CurrentStatus,
         NewState     => RawNewState,
         ResponseCode => ResponseCode);

      if ResponseCode = Interface.ResponseCodeT'Pos(Interface.Success) then

         NewState := GetReaderState(RawNewState);
         ProcessReaderStateChange;
         if NewState in Interface.ValidReaderStateT then
            SetCurrentStatus(TheStatus => NewState);
         else
            SetCurrentStatus(TheStatus => Interface.Unaware);
         end if;

      elsif ResponseCode = Interface.ResponseCodeT'Pos(Interface.Timedout)then

         -- no change to the state.
         null;

      else

         MarkTokenAbsent;
         SetCurrentStatus(TheStatus => Interface.Unaware);

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

      if ReaderStatus(Reader).CurrentStatus = Interface.CardPresent and
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
   --#        in Interface.ReaderStatus;
   --#        in Interface.ReaderInput;
   --# derives Found   from ReaderStatus,
   --#                      Interface.ReaderStatus,
   --#                      Reader,
   --#                      CertType &
   --#         RawCert from ReaderStatus,
   --#                      Interface.ReaderStatus,
   --#                      Interface.ReaderInput,
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
               Interface.GetIDCert
                 (CardHandle   => ReaderStatus(Reader).TokenHandle,
                  RawIDCert    => RawCert,
                  StatusOK     => StatusOK,
                  ResponseCode => ResponseCode);
            when CertTypes.AuthCert =>
               Interface.GetAuthCert
                 (CardHandle   => ReaderStatus(Reader).TokenHandle,
                  RawAuthCert  => RawCert,
                  StatusOK     => StatusOK,
                  Exists       => Exists,
                  ResponseCode => ResponseCode);
            when CertTypes.PrivCert =>
               Interface.GetPrivCert
                 (CardHandle   => ReaderStatus(Reader).TokenHandle,
                  RawPrivCert  => RawCert,
                  StatusOK     => StatusOK,
                  ResponseCode => ResponseCode);
            when CertTypes.IandACert =>
               Interface.GetIACert
                 (CardHandle   => ReaderStatus(Reader).TokenHandle,
                  RawIACert  => RawCert,
                  StatusOK     => StatusOK,
                  ResponseCode => ResponseCode);
         end case;

         Found := StatusOK and Exists and
              (ResponseCode = Interface.ResponseCodeT'Pos(Interface.Success));

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
   --#        in     Interface.ReaderStatus;
   --#           out Interface.ReaderOutput;
   --# derives Interface.ReaderOutput from ReaderStatus,
   --#                                     Interface.ReaderStatus,
   --#                                     RawCert &
   --#         Success                from ReaderStatus,
   --#                                     Interface.ReaderStatus;

   is
      StatusOK     : Boolean;
      ResponseCode : BasicTypes.Unsigned32T;
   begin
        Interface.UpdateAuthCert
         (CardHandle   => ReaderStatus(User).TokenHandle ,
          RawAuthCert  => RawCert,
          StatusOK     => StatusOK,
          ResponseCode => ResponseCode);

        Success := StatusOK and
              (ResponseCode = Interface.ResponseCodeT'Pos(Interface.Success));

   end WriteAuthCertificate;

end TokenReader;
