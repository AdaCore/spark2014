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
-- UserToken
--
-- Description:
--    ...
--
------------------------------------------------------------------
with BasicTypes;
use type BasicTypes.PresenceT;

with TokenTypes;
use type TokenTypes.TryT;
use type TokenTypes.TokenIDT;

with CertTypes;
use type CertTypes.IDT;

with PrivTypes;
use type PrivTypes.ClassT;

with AuditLog;
with Cert;
with Cert.ID;
with Cert.Attr;
with Cert.Attr.Priv;
with Cert.Attr.Auth;
with Cert.Attr.IandA;
with CertProcessing;
with UserToken.Interface;
with CryptoTypes;
with Clock;
with ConfigData;
with KeyStore;
with CertificateStore;

package body UserToken
--# own State  is TokenPresence,
--#               TokenTry,
--#               TokenID,
--#               IDCert,
--#               IandACert,
--#               AuthCert,
--#               PrivCert,
--#               UserToken.Interface.State &
--#     Status is UserToken.Interface.Status &
--#     Input  is in UserToken.Interface.Input &
--#     Output is out UserToken.Interface.Output;
is


   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   type CertificateStatus is (Bad, NotVerified, NotCurrent, ValidCert);


   type ValidIDCertT is record
      Valid    : Boolean;
      IDStatus : CertificateStatus;
      Contents : Cert.ID.ContentsT;
   end record;


   type ValidPrivCertT is record
      Valid    : Boolean;
      Contents : Cert.Attr.Priv.ContentsT;
   end record;

   type ValidAuthCertT is record
      Valid    : Boolean;
      Contents : Cert.Attr.Auth.ContentsT;
   end record;

   type ValidIandACertT is record
      Valid    : Boolean;
      Contents : Cert.Attr.IandA.ContentsT;
   end record;

   ------------------------------------------------------------------
   -- State
   --
   ------------------------------------------------------------------
   TokenPresence : BasicTypes.PresenceT;

   TokenTry  : TokenTypes.TryT;

   TokenID   : TokenTypes.TokenIDT;

   IDCert    : ValidIDCertT;

   IandACert : ValidIandACertT;
   AuthCert  : ValidAuthCertT;
   PrivCert  : ValidPrivCertT;

   ------------------------------------------------------------------
   -- Local Operations
   --
   ------------------------------------------------------------------
   ------------------------------------------------------------------
   -- ClearIDCert
   --
   -- Description:
   --    Clears and ID Certificate.
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure ClearIDCert
   --# global out IDCert;
   --# derives IDCert from ;
   is

      IDCertContents    : Cert.ID.ContentsT;

   begin
      Cert.ID.Clear(IDCertContents);
      IDCert := ValidIDCertT'(Valid    => False,
                              IDStatus => Bad,
                              Contents => IDCertContents);

   end ClearIDCert;

   ------------------------------------------------------------------
   -- Public Operations
   --
   ------------------------------------------------------------------

   ------------------------------------------------------------------
   -- Clear
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure Clear
   --# global out IDCert;
   --#        out TokenPresence;
   --#        out TokenTry;
   --#        out TokenID;
   --#        out IandACert;
   --#        out AuthCert;
   --#        out PrivCert;
   --# derives IDCert,
   --#         TokenPresence,
   --#         TokenTry,
   --#         TokenID,
   --#         IandACert,
   --#         AuthCert,
   --#         PrivCert      from ;
   is

      AuthCertContents  : Cert.Attr.Auth.ContentsT;
      PrivCertContents  : Cert.Attr.Priv.ContentsT;
      IandACertContents : Cert.Attr.IandA.ContentsT;

   begin
      TokenPresence := BasicTypes.Absent;
      TokenTry      := TokenTypes.NoToken;
      TokenID       := TokenTypes.TokenIDT'First;

      ClearIDCert;

      Cert.Attr.Auth.Clear(AuthCertContents);
      AuthCert := ValidAuthCertT'(Valid    => False,
                                  Contents => AuthCertContents);

      Cert.Attr.Priv.Clear(PrivCertContents);
      PrivCert := ValidPrivCertT'(Valid    => False,
                                  Contents => PrivCertContents);

      Cert.Attr.IandA.Clear(IandACertContents);
      IandACert := ValidIandACertT'(Valid    => False,
                                    Contents => IandACertContents);

   end Clear;

   ------------------------------------------------------------------
   -- Init
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------

   procedure Init
   --# global in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out Interface.Status;
   --#        in out AuditLog.FileState;
   --#        in out AuditLog.State;
   --#           out IDCert;
   --#           out TokenPresence;
   --#           out TokenTry;
   --#           out TokenID;
   --#           out IandACert;
   --#           out AuthCert;
   --#           out PrivCert;
   --#           out Interface.State;
   --# derives IDCert,
   --#         TokenPresence,
   --#         TokenTry,
   --#         TokenID,
   --#         IandACert,
   --#         AuthCert,
   --#         PrivCert           from  &
   --#         Interface.Status,
   --#         Interface.State    from Interface.Status &
   --#         AuditLog.FileState,
   --#         AuditLog.State     from Interface.Status,
   --#                                 AuditLog.FileState,
   --#                                 AuditLog.State,
   --#                                 Clock.Now,
   --#                                 ConfigData.State;
   is
   begin
      Interface.Init;
      Clear;
   end Init;

   ------------------------------------------------------------------
   -- Poll
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure Poll
   --# global in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in     Interface.Input;
   --#        in out Interface.Status;
   --#        in out Interface.State;
   --#        in out AuditLog.FileState;
   --#        in out AuditLog.State;
   --#           out TokenPresence;
   --# derives TokenPresence,
   --#         Interface.State    from Interface.Status,
   --#                                 Interface.State,
   --#                                 Interface.Input &
   --#         Interface.Status   from * &
   --#         AuditLog.FileState from *,
   --#                                 Interface.Status,
   --#                                 Interface.State,
   --#                                 AuditLog.State,
   --#                                 Clock.Now &
   --#         AuditLog.State     from *,
   --#                                 Interface.Status,
   --#                                 Interface.State,
   --#                                 AuditLog.FileState,
   --#                                 Clock.Now,
   --#                                 ConfigData.State;
   is
   begin
      Interface.Poll;
      TokenPresence := Interface.TheTokenPresence;
   end Poll;

   ------------------------------------------------------------------
   -- UpdateAuthCert
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure UpdateAuthCert (Success : out Boolean)
   --# global in     AuthCert;
   --#        in     Interface.State;
   --#        in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in     KeyStore.Store;
   --#        in out Interface.Status;
   --#        in out AuditLog.FileState;
   --#        in out AuditLog.State;
   --#           out Interface.Output;
   --# derives Success,
   --#         Interface.Output   from AuthCert,
   --#                                 Interface.Status,
   --#                                 Interface.State,
   --#                                 KeyStore.Store &
   --#         Interface.Status   from *,
   --#                                 AuthCert,
   --#                                 KeyStore.Store &
   --#         AuditLog.FileState from *,
   --#                                 AuthCert,
   --#                                 AuditLog.State,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 KeyStore.Store &
   --#         AuditLog.State     from *,
   --#                                 AuthCert,
   --#                                 AuditLog.FileState,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 KeyStore.Store;
   is
      SignedOK   : Boolean;
      Signature  : CertTypes.SignatureT;
      RawCert,
      SignedCert : CertTypes.RawCertificateT;

   begin
      Cert.Attr.Auth.Construct
        (Contents => AuthCert.Contents,
         RawCert  => RawCert);

      KeyStore.Sign
        (RawCertData => Cert.GetData(RawCert),
         Signature   => Signature,
         Signed      => SignedOK);

       -- Add signature to raw data.
       if SignedOK then
          CertProcessing.AddAuthSignature(RawCert, Signature, SignedCert);

          Interface.WriteAuthCertificate
            (RawCert => SignedCert,
             Success => Success);

       else
          Success := False;
       end if;

   end UpdateAuthCert;

   ------------------------------------------------------------------
   -- ExtractUser
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   function ExtractUser return AuditTypes.UserTextT
   --# global IDCert,
   --#        TokenTry,
   --#        IandACert,
   --#        AuthCert,
   --#        PrivCert;
   is
      Result : AuditTypes.UserTextT;
   begin
      if TokenTry = TokenTypes.GoodToken then
         if IDCert.Valid then
            Result := Cert.ID.ExtractUser(IDCert.Contents);
         elsif AuthCert.Valid then
            Result := Cert.Attr.Auth.ExtractUser(AuthCert.Contents);
         elsif PrivCert.Valid then
            Result := Cert.Attr.Priv.ExtractUser(PrivCert.Contents);
         elsif IandACert.Valid then
            Result := Cert.Attr.IandA.ExtractUser(IandACert.Contents);
         else
            Result := AuditTypes.NoUser;
         end if;
      else
         Result := AuditTypes.NoUser;
      end if;
      return Result;
   end ExtractUser;

   ------------------------------------------------------------------
   -- IsPresent
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   function IsPresent return Boolean
   --# global TokenPresence;
   is
   begin
      return TokenPresence = BasicTypes.Present;
   end IsPresent;
   ------------------------------------------------------------------
   -- ReadAndCheckAuthCert
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure ReadAndCheckAuthCert(AuthCertOK :    out Boolean)
   --# global in     Interface.State;
   --#        in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in     Interface.Input;
   --#        in     KeyStore.Store;
   --#        in     Clock.CurrentTime;
   --#        in     KeyStore.State;
   --#        in out TokenID;
   --#        in out Interface.Status;
   --#        in out AuditLog.FileState;
   --#        in out AuditLog.State;
   --#           out IDCert;
   --#           out TokenTry;
   --#           out AuthCert;
   --# derives TokenID,
   --#         Interface.Status   from *,
   --#                                 Interface.State &
   --#         AuthCert,
   --#         AuthCertOK         from Interface.Status,
   --#                                 Interface.State,
   --#                                 Interface.Input,
   --#                                 KeyStore.Store,
   --#                                 Clock.CurrentTime,
   --#                                 KeyStore.State &
   --#         AuditLog.FileState,
   --#         AuditLog.State     from Interface.Status,
   --#                                 Interface.State,
   --#                                 AuditLog.FileState,
   --#                                 AuditLog.State,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 Interface.Input,
   --#                                 KeyStore.Store &
   --#         IDCert             from Interface.Status,
   --#                                 Interface.State,
   --#                                 Interface.Input,
   --#                                 KeyStore.Store &
   --#         TokenTry           from Interface.State;
   is
      AuthValid : Boolean;

      AuthCertContents : Cert.Attr.Auth.ContentsT;

   ------------------------------------------------------------------
   -- CheckIDCertOK
   --
   -- Description:
   --    Checks that the ID Cert is present and valid.
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure CheckIDCertOK
     --# global in     TokenID;
     --#        in     Interface.State;
     --#        in     Clock.Now;
     --#        in     ConfigData.State;
     --#        in     Interface.Input;
     --#        in     KeyStore.Store;
     --#        in out Interface.Status;
     --#        in out AuditLog.FileState;
     --#        in out AuditLog.State;
     --#           out IDCert;
     --# derives AuditLog.FileState,
     --#         AuditLog.State     from Interface.Status,
     --#                                 Interface.State,
     --#                                 AuditLog.FileState,
     --#                                 AuditLog.State,
     --#                                 Clock.Now,
     --#                                 ConfigData.State,
     --#                                 Interface.Input,
     --#                                 KeyStore.Store &
     --#         IDCert             from TokenID,
     --#                                 Interface.Status,
     --#                                 Interface.State,
     --#                                 Interface.Input,
     --#                                 KeyStore.Store &
     --#         Interface.Status   from *;
   is
      RawCert   : CertTypes.RawCertificateT;

      CertFound : Boolean;
      IDValid   : Boolean;
      IDStatus  : CertificateStatus;
      ExtractOK,
        Verified,
        TokenIDMatches : Boolean := False;

      IDCertContents : Cert.ID.ContentsT;

   begin
      Cert.ID.Clear(IDCertContents);

      Interface.GetCertificate
        (CertType => CertTypes.IDCert,
         RawCert  => RawCert,
         Found    => CertFound);

      if CertFound then

         Cert.ID.Extract
           (RawCert  => RawCert,
            Contents => IDCertContents,
            Success  => ExtractOK);

         if ExtractOK then

            TokenIDMatches :=
              (TokenID =
               TokenTypes.TokenIDT(Cert.ID.TheID
                (Contents => IDCertContents).SerialNumber));

            Cert.ID.IsOK
              ( RawCert => RawCert,
                Contents => IDCertContents,
                IsVerified => Verified);

         end if;
      end if;

      IDValid := CertFound and ExtractOK
        and TokenIDMatches and Verified;

      if not CertFound or not ExtractOK or not TokenIDMatches then
         IDStatus := Bad;
      elsif not Verified then
         IDStatus := NotVerified;
      else
         IDStatus := ValidCert;
      end if;

      IDCert := ValidIDCertT'( Valid    => IDValid,
                               IDStatus => IDStatus,
                               Contents => IDCertContents);

   end CheckIDCertOK;


      ------------------------------------------------------------------
      -- CheckAuthCert
      --
      -- Description:
      --    Performs the checks on an Auth Cert.
      --
      -- Implementation Notes:
      --    None.
      ------------------------------------------------------------------
      procedure CheckAuthCert
        --# global in     IDCert;
        --#        in     Interface.State;
        --#        in     Clock.Now;
        --#        in     ConfigData.State;
        --#        in     Interface.Input;
        --#        in     KeyStore.Store;
        --#        in     Clock.CurrentTime;
        --#        in     KeyStore.State;
        --#        in out Interface.Status;
        --#        in out AuditLog.FileState;
        --#        in out AuditLog.State;
        --#        in out AuthCertContents;
        --#           out AuthValid;
        --# derives AuditLog.FileState,
        --#         AuditLog.State     from Interface.Status,
        --#                                 Interface.State,
        --#                                 AuditLog.FileState,
        --#                                 AuditLog.State,
        --#                                 Clock.Now,
        --#                                 ConfigData.State,
        --#                                 Interface.Input,
        --#                                 KeyStore.Store &
        --#         Interface.Status   from * &
        --#         AuthValid          from IDCert,
        --#                                 Interface.Status,
        --#                                 Interface.State,
        --#                                 Interface.Input,
        --#                                 KeyStore.Store,
        --#                                 Clock.CurrentTime,
        --#                                 KeyStore.State &
        --#         AuthCertContents   from *,
        --#                                 Interface.Status,
        --#                                 Interface.State,
        --#                                 Interface.Input;
      is
         RawCert : CertTypes.RawCertificateT;

         CertFound : Boolean;
         ExtractOK,
           Verified,
           Current,
           BaseIDMatches : Boolean := False;

      begin
         Interface.GetCertificate
           (CertType => CertTypes.AuthCert,
            RawCert  => RawCert,
            Found    => CertFound);

         if CertFound then
            Cert.Attr.Auth.Extract
              (RawCert  => RawCert,
               Contents => AuthCertContents,
               Success  => ExtractOK);

            if ExtractOK then

               BaseIDMatches :=
                 (Cert.ID.TheID
                   (Contents => IDCert.Contents) =
                  Cert.Attr.Auth.TheBaseCert
                   (Contents => AuthCertContents));

               Cert.Attr.Auth.IsOK
                 ( RawCert => RawCert,
                   Contents => AuthCertContents,
                   IsVerified => Verified);

               Current := Cert.Attr.Auth.IsCurrent
                 (Contents => AuthCertContents);

            end if;

         end if;

         AuthValid := CertFound and ExtractOK
                    and BaseIDMatches and Verified and Current;

      end CheckAuthCert;

   -----------------------------------------------------------------
   -- begin ReadAndCheckAuthCert
   -----------------------------------------------------------------
   begin

      ClearIDCert;

      TokenTry := Interface.TheTokenTry;

      Cert.Attr.Auth.Clear(Contents => AuthCertContents);

      if TokenTry = TokenTypes.GoodToken then
         TokenID  := Interface.TheTokenID;

         CheckIDCertOK;

         CheckAuthCert;

      else
         AuthValid := False;
      end if;

      AuthCert := ValidAuthCertT'
        (Valid    => AuthValid,
         Contents => AuthCertContents);

      AuthCertOK := AuthValid and IDCert.Valid;

   end ReadAndCheckAuthCert;


   ------------------------------------------------------------------
   -- ReadAndCheck
   --
   -- Implementation Notes:
   --    Note the ID cert, TokenID and TokenTry status will already have
   --    been read as part of checking the auth cert.
   ------------------------------------------------------------------
   procedure ReadAndCheck
     (Description :    out AuditTypes.DescriptionT;
      TokenOK     :    out Boolean)
   --# global in     TokenTry;
   --#        in     Interface.State;
   --#        in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in     Interface.Input;
   --#        in     KeyStore.Store;
   --#        in     Clock.CurrentTime;
   --#        in out IDCert;
   --#        in out Interface.Status;
   --#        in out AuditLog.FileState;
   --#        in out AuditLog.State;
   --#           out IandACert;
   --#           out PrivCert;
   --# derives IandACert,
   --#         PrivCert,
   --#         Description,
   --#         TokenOK            from IDCert,
   --#                                 TokenTry,
   --#                                 Interface.Status,
   --#                                 Interface.State,
   --#                                 Interface.Input,
   --#                                 KeyStore.Store,
   --#                                 Clock.CurrentTime &
   --#         AuditLog.FileState,
   --#         AuditLog.State     from TokenTry,
   --#                                 Interface.Status,
   --#                                 Interface.State,
   --#                                 AuditLog.FileState,
   --#                                 AuditLog.State,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 Interface.Input,
   --#                                 KeyStore.Store &
   --#         IDCert             from *,
   --#                                 TokenTry,
   --#                                 Clock.CurrentTime &
   --#         Interface.Status   from *,
   --#                                 TokenTry;
   is
      IandACertContents : Cert.Attr.IandA.ContentsT;
      PrivCertContents  : Cert.Attr.Priv.ContentsT;
      PrivValid, IandAValid : Boolean;

      ------------------------------------------------------------------
      -- MakeDescription
      --
      -- Description:
      --    Constructs a description from a piece of text,
      --    truncating if required.
      --
      -- Implementation Notes:
      --    Hidden from SPARK because of use of slicing.
      ------------------------------------------------------------------
      function MakeDescription (Text : in String)
                                return AuditTypes.DescriptionT
      is
         --# hide MakeDescription;
         Result : AuditTypes.DescriptionT := AuditTypes.NoDescription;
      begin
         if Text'Last < Result'Last then
            Result( 1 .. Text'Last) := Text;
         else
            Result := Text( 1 .. Result'Last);
         end if;
         return Result;

      end MakeDescription;

      ------------------------------------------------------------------
      -- CheckIDCert
      --
      -- Description:
      --    Performs the checks on an ID Cert.
      --
      -- Implementation Notes:
      --    None.
      ------------------------------------------------------------------
      procedure CheckIDCert
        --# global in     Clock.CurrentTime;
        --#        in out IDCert;
        --#           out Description;
        --# derives IDCert,
        --#         Description from IDCert,
        --#                          Clock.CurrentTime;
      is
           Current : Boolean;
           IDCertContents : Cert.ID.ContentsT;

      begin

         if IDCert.Valid then

            IDCertContents := IDCert.Contents;
            Current := Cert.ID.IsCurrent
              (Contents => IDCertContents);

            IDCert.Valid := IDCert.Valid and Current;

            if not Current then
               IDCert.IDStatus := NotCurrent;
            end if;

         end if;

         case IDCert.IDStatus is
            when Bad =>
               Description := MakeDescription("ID Certificate Bad");
            when NotVerified =>
               Description :=
                 MakeDescription("ID Certificate Not Verifiable");
            when NotCurrent =>
               Description :=
                 MakeDescription("ID Certificate Not Current");
            when ValidCert =>
               Description := AuditTypes.NoDescription;
         end case;

      end CheckIDCert;

      ------------------------------------------------------------------
      -- CheckPrivCert
      --
      -- Description:
      --    Performs the checks on an Priv Cert.
      --
      -- Implementation Notes:
      --    None.
      ------------------------------------------------------------------
      procedure CheckPrivCert
        --# global in     IDCert;
        --#        in     Interface.State;
        --#        in     Clock.Now;
        --#        in     ConfigData.State;
        --#        in     Interface.Input;
        --#        in     KeyStore.Store;
        --#        in     Clock.CurrentTime;
        --#        in out Interface.Status;
        --#        in out AuditLog.FileState;
        --#        in out AuditLog.State;
        --#        in out Description;
        --#        in out PrivCertContents;
        --#           out PrivValid;
        --# derives AuditLog.FileState,
        --#         AuditLog.State     from Interface.Status,
        --#                                 Interface.State,
        --#                                 AuditLog.FileState,
        --#                                 AuditLog.State,
        --#                                 Clock.Now,
        --#                                 ConfigData.State,
        --#                                 Interface.Input,
        --#                                 KeyStore.Store &
        --#         Interface.Status   from * &
        --#         Description        from *,
        --#                                 IDCert,
        --#                                 Interface.Status,
        --#                                 Interface.State,
        --#                                 Interface.Input,
        --#                                 KeyStore.Store,
        --#                                 Clock.CurrentTime &
        --#         PrivValid          from IDCert,
        --#                                 Interface.Status,
        --#                                 Interface.State,
        --#                                 Interface.Input,
        --#                                 KeyStore.Store,
        --#                                 Clock.CurrentTime &
        --#         PrivCertContents   from *,
        --#                                 Interface.Status,
        --#                                 Interface.State,
        --#                                 Interface.Input;
      is
         RawCert : CertTypes.RawCertificateT;
         IDCertContents : Cert.ID.ContentsT;

         CertFound : Boolean;
         ExtractOK,
           Verified,
           Current,
           BaseIDMatches : Boolean := False;

      begin
         Interface.GetCertificate
           (CertType => CertTypes.PrivCert,
            RawCert  => RawCert,
            Found    => CertFound);

         if CertFound then
            Cert.Attr.Priv.Extract
              (RawCert  => RawCert,
               Contents => PrivCertContents,
               Success  => ExtractOK);

            if ExtractOK then

               IDCertContents := IDCert.Contents;
               BaseIDMatches :=
                 (Cert.ID.TheID
                   (Contents => IDCertContents) =
                  Cert.Attr.Priv.TheBaseCert
                   (Contents => PrivCertContents));

               Cert.Attr.Priv.IsOK
                 ( RawCert => RawCert,
                   Contents => PrivCertContents,
                   IsVerified => Verified);

               Current := Cert.Attr.Priv.IsCurrent
                 (Contents => PrivCertContents);

            end if;

         end if;

         PrivValid := CertFound and ExtractOK
                    and BaseIDMatches and Verified and Current;

         if Description = AuditTypes.NoDescription then
            if not CertFound or not ExtractOK or not BaseIDMatches then
               Description := MakeDescription("Privilege Certificate Bad");
            elsif not Verified then
               Description :=
                 MakeDescription("Privilege Certificate Not Verifiable");
            elsif not Current then
               Description :=
                 MakeDescription("Privilege Certificate Not Current");
            end if;
         end if;
      end CheckPrivCert;

      ------------------------------------------------------------------
      -- CheckIandACert
      --
      -- Description:
      --    Performs the checks on an I&A Cert.
      --
      -- Implementation Notes:
      --    None.
      ------------------------------------------------------------------
      procedure CheckIandACert
        --# global in     IDCert;
        --#        in     Interface.State;
        --#        in     Clock.Now;
        --#        in     ConfigData.State;
        --#        in     Interface.Input;
        --#        in     KeyStore.Store;
        --#        in     Clock.CurrentTime;
        --#        in out Interface.Status;
        --#        in out AuditLog.FileState;
        --#        in out AuditLog.State;
        --#        in out Description;
        --#        in out IandACertContents;
        --#           out IandAValid;
        --# derives AuditLog.FileState,
        --#         AuditLog.State     from Interface.Status,
        --#                                 Interface.State,
        --#                                 AuditLog.FileState,
        --#                                 AuditLog.State,
        --#                                 Clock.Now,
        --#                                 ConfigData.State,
        --#                                 Interface.Input,
        --#                                 KeyStore.Store &
        --#         Interface.Status   from * &
        --#         Description        from *,
        --#                                 IDCert,
        --#                                 Interface.Status,
        --#                                 Interface.State,
        --#                                 Interface.Input,
        --#                                 KeyStore.Store,
        --#                                 Clock.CurrentTime &
        --#         IandAValid         from IDCert,
        --#                                 Interface.Status,
        --#                                 Interface.State,
        --#                                 Interface.Input,
        --#                                 KeyStore.Store,
        --#                                 Clock.CurrentTime &
        --#         IandACertContents  from *,
        --#                                 Interface.Status,
        --#                                 Interface.State,
        --#                                 Interface.Input;
      is
         RawCert : CertTypes.RawCertificateT;
         IDCertContents : Cert.ID.ContentsT;

         CertFound : Boolean;
         ExtractOK,
           Verified,
           Current,
           BaseIDMatches : Boolean := False;

      begin
         Interface.GetCertificate
           (CertType => CertTypes.IandACert,
            RawCert  => RawCert,
            Found    => CertFound);

         if CertFound then
            Cert.Attr.IandA.Extract
              (RawCert  => RawCert,
               Contents => IandACertContents,
               Success  => ExtractOK);

            if ExtractOK then

               IDCertContents := IDCert.Contents;
               BaseIDMatches :=
                 (Cert.ID.TheID
                   (Contents => IDCertContents) =
                  Cert.Attr.IandA.TheBaseCert
                   (Contents => IandACertContents));

               Cert.Attr.IandA.IsOK
                 ( RawCert => RawCert,
                   Contents => IandACertContents,
                   IsVerified => Verified);

               Current := Cert.Attr.IandA.IsCurrent
                 (Contents => IandACertContents);


            end if;
         end if;

         IandAValid := CertFound and ExtractOK
                    and BaseIDMatches and Verified and Current;

         if Description = AuditTypes.NoDescription then
            if not CertFound or not ExtractOK or not BaseIDMatches then
               Description := MakeDescription("I&A Certificate Bad");
            elsif not Verified then
               Description :=
                 MakeDescription("I&A Certificate Not Verifiable");
            elsif not Current then
               Description :=
                 MakeDescription("I&A Certificate Not Current");
            end if;
         end if;
      end CheckIandACert;


   -----------------------------------------------------------------
   -- begin ReadAndCheck
   -----------------------------------------------------------------
   begin

      Cert.Attr.IandA.Clear(Contents => IandACertContents);
      Cert.Attr.Priv.Clear(Contents => PrivCertContents);

      if TokenTry = TokenTypes.GoodToken then

         CheckIDCert;

         CheckPrivCert;

         CheckIandACert;

      else
         PrivValid   := False;
         IandAValid  := False;
         Description := MakeDescription("Token Bad");
      end if;

      TokenOK := IDCert.Valid and IandAValid and PrivValid;

      PrivCert := ValidPrivCertT'
        (Valid    => PrivValid,
         Contents => PrivCertContents);

      IandACert := ValidIandACertT'
        (Valid    => IandAValid,
         Contents => IandACertContents);

   end ReadAndCheck;

   ------------------------------------------------------------------
   -- AddAuthCert
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure AddAuthCert( Success : out Boolean)
   --# global in     IDCert;
   --#        in     PrivCert;
   --#        in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in     Clock.CurrentTime;
   --#        in     KeyStore.State;
   --#        in     CertificateStore.State;
   --#        in out AuditLog.FileState;
   --#        in out AuditLog.State;
   --#           out AuthCert;
   --# derives AuthCert           from IDCert,
   --#                                 PrivCert,
   --#                                 ConfigData.State,
   --#                                 Clock.CurrentTime,
   --#                                 KeyStore.State,
   --#                                 CertificateStore.State &
   --#         AuditLog.FileState,
   --#         AuditLog.State     from AuditLog.FileState,
   --#                                 AuditLog.State,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 CertificateStore.State &
   --#         Success            from CertificateStore.State;
   --# pre KeyStore.PrivateKeyPresent(KeyStore.State);
   is
      ID         : CertTypes.IDT;
      NotBefore  : Clock.TimeT;
      NotAfter   : Clock.TimeT;
      Clearance  : PrivTypes.ClearanceT;

      IDCertContents : Cert.ID.ContentsT;
      AuthCertContents : Cert.Attr.Auth.ContentsT;
   begin

      Clearance.Class := Cert.Attr.Priv.TheClearance(PrivCert.Contents).Class;
      if Clearance.Class > ConfigData.TheEnclaveClearance then
         Clearance.Class := ConfigData.TheEnclaveClearance;
      end if;

      if ConfigData.AuthPeriodIsEmpty then
         NotBefore := Clock.TheCurrentTime;
         NotAfter  := Clock.ZeroTime;
      else
         ConfigData.GetAuthPeriod
           (TheTime   => Clock.TheCurrentTime,
            NotBefore => NotBefore,
            NotAfter  => NotAfter);
      end if;

      ID.Issuer := KeyStore.ThisTIS;

      if not CertificateStore.SerialNumberHasOverflowed then
         ID.SerialNumber := CertificateStore.SerialNumber;
         Success := True;
      else
         ID.SerialNumber := CertTypes.SerialNumberT'First;

         AuditLog.AddElementToLog
           ( ElementID   => AuditTypes.SystemFault,
             Severity    => AuditTypes.Warning,
             User        => AuditTypes.NoUser,
             Description => "No Serial Numbers avaiable for issue of Authorisation Certificate"
             );
         Success := False;
      end if;

      IDCertContents := IDCert.Contents;
      Cert.Attr.Auth.SetContents
        ( ID         => ID,
          NotBefore  => NotBefore,
          NotAfter   => NotAfter,
          Mechanism  => CryptoTypes.SHA1_RSA,
          BaseCertID => Cert.ID.TheID(IDCertContents),
          Role       => Cert.Attr.Priv.TheRole(PrivCert.Contents),
          Clearance  => Clearance,
          Contents   => AuthCertContents);

      AuthCert :=
        ValidAuthCertT'(Valid    => True,
                        Contents => AuthCertContents
                        );
   end AddAuthCert;

   ------------------------------------------------------------------
   -- GetIandATemplate
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   function GetIandATemplate return IandATypes.TemplateT
   --# global IandACert;
   is
   begin
      return Cert.Attr.IandA.TheTemplate(IandACert.Contents);
   end GetIandATemplate;


   ------------------------------------------------------------------
   -- GetClass
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   function GetClass return PrivTypes.ClassT
   --# global AuthCert;
   is
   begin
      return Cert.Attr.Auth.TheClearance(AuthCert.Contents).Class;
   end GetClass;



end UserToken;
