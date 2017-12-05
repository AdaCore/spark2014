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
with CommonTypes;
use type CommonTypes.PresenceT;

with TokenTypes;
use type TokenTypes.TryT;
use type TokenTypes.TokenIDT;

with CertTypes;
use type CertTypes.IDT;

with PrivTypes;
use type PrivTypes.ClassT;

with AuditLog,
     Cert,
     Cert.ID,
     Cert.Attr,
     Cert.Attr.Priv,
     Cert.Attr.Auth,
     Cert.Attr.IandA,
     CertProcessing,
     CertificateStore,
     Clock,
     ConfigData,
     CryptoTypes,
     KeyStore,
     UserToken.Interfac;

package body UserToken
  with Refined_State => (State  => (TokenPresence,
                                    TokenTry,
                                    TokenID,
                                    IDCert,
                                    IandACert,
                                    AuthCert,
                                    PrivCert,
                                    UserToken.Interfac.State),
                         Status => UserToken.Interfac.Status,
                         Input  => UserToken.Interfac.Input,
                         Output => UserToken.Interfac.Output)
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
   TokenPresence : CommonTypes.PresenceT;

   TokenTry      : TokenTypes.TryT;

   TokenID       : TokenTypes.TokenIDT;

   IDCert        : ValidIDCertT;

   IandACert     : ValidIandACertT;
   AuthCert      : ValidAuthCertT;
   PrivCert      : ValidPrivCertT;

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
     with Global  => (Output => IDCert),
          Depends => (IDCert => null)
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
     with Refined_Global  => (Output => (AuthCert,
                                         IandACert,
                                         IDCert,
                                         PrivCert,
                                         TokenID,
                                         TokenPresence,
                                         TokenTry)),
          Refined_Depends => ((AuthCert,
                               IandACert,
                               IDCert,
                               PrivCert,
                               TokenID,
                               TokenPresence,
                               TokenTry)      => null)
   is
      AuthCertContents  : Cert.Attr.Auth.ContentsT;
      PrivCertContents  : Cert.Attr.Priv.ContentsT;
      IandACertContents : Cert.Attr.IandA.ContentsT;
   begin
      TokenPresence := CommonTypes.Absent;
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
     with Refined_Global  => (Input  => (Clock.Now,
                                         ConfigData.State),
                              Output => (AuthCert,
                                         IandACert,
                                         IDCert,
                                         Interfac.State,
                                         PrivCert,
                                         TokenID,
                                         TokenPresence,
                                         TokenTry),
                              In_Out => (AuditLog.FileState,
                                         AuditLog.State,
                                         Interfac.Status)),
          Refined_Depends => ((AuditLog.FileState,
                               AuditLog.State)     => (AuditLog.FileState,
                                                       AuditLog.State,
                                                       Clock.Now,
                                                       ConfigData.State,
                                                       Interfac.Status),
                              (AuthCert,
                               IandACert,
                               IDCert,
                               PrivCert,
                               TokenID,
                               TokenPresence,
                               TokenTry)           => null,
                              (Interfac.State,
                               Interfac.Status)    => Interfac.Status)
   is
   begin
      Interfac.Init;
      Clear;
   end Init;

   ------------------------------------------------------------------
   -- Poll
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure Poll
     with Refined_Global  => (Input  => (Clock.Now,
                                         ConfigData.State,
                                         Interfac.Input),
                              Output => TokenPresence,
                              In_Out => (AuditLog.FileState,
                                         AuditLog.State,
                                         Interfac.State,
                                         Interfac.Status)),
          Refined_Depends => (AuditLog.FileState =>+ (AuditLog.State,
                                                      Clock.Now,
                                                      Interfac.State,
                                                      Interfac.Status),
                              AuditLog.State     =>+ (AuditLog.FileState,
                                                      Clock.Now,
                                                      ConfigData.State,
                                                      Interfac.State,
                                                      Interfac.Status),
                              (Interfac.State,
                               TokenPresence)    => (Interfac.Input,
                                                     Interfac.State,
                                                     Interfac.Status),
                              Interfac.Status    =>+ null)
   is
   begin
      Interfac.Poll;
      TokenPresence := Interfac.TheTokenPresence;
   end Poll;

   ------------------------------------------------------------------
   -- UpdateAuthCert
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure UpdateAuthCert (Success : out Boolean)
     with Refined_Global  => (Input  => (AuthCert,
                                         Clock.Now,
                                         ConfigData.State,
                                         Interfac.State,
                                         KeyStore.Store),
                              In_Out => (AuditLog.FileState,
                                         AuditLog.State,
                                         Interfac.Output,
                                         Interfac.Status)),
          Refined_Depends => ((AuditLog.FileState,
                               AuditLog.State)     => (AuditLog.FileState,
                                                       AuditLog.State,
                                                       AuthCert,
                                                       Clock.Now,
                                                       ConfigData.State,
                                                       KeyStore.Store),
                              Interfac.Output      =>+ (AuthCert,
                                                        Interfac.State,
                                                        Interfac.Status,
                                                        KeyStore.Store),
                              Success              => (AuthCert,
                                                       Interfac.State,
                                                       Interfac.Status,
                                                       KeyStore.Store),
                              Interfac.Status      =>+ (AuthCert,
                                                        KeyStore.Store))
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

          Interfac.WriteAuthCertificate
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
     with Refined_Global => (AuthCert,
                             IandACert,
                             IDCert,
                             PrivCert,
                             TokenTry)
   is
      Result : AuditTypes.UserTextT;
   begin
      if TokenTry = TokenTypes.GoodToken then
         if IDCert.Valid then
            Result := Cert.ExtractUser
              (Cert.ID.Cert_Id_To_Cert (IDCert.Contents));
         elsif AuthCert.Valid then
            Result := Cert.ExtractUser
              (Cert.Attr.Auth.Cert_Attr_Auth_To_Cert (AuthCert.Contents));
         elsif PrivCert.Valid then
            Result := Cert.ExtractUser
              (Cert.Attr.Priv.Cert_Attr_Priv_To_Cert (PrivCert.Contents));
         elsif IandACert.Valid then
            Result := Cert.ExtractUser
              (Cert.Attr.IandA.Cert_Attr_IandA_To_Cert (IandACert.Contents));
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
   function IsPresent return Boolean is (TokenPresence = CommonTypes.Present)
     with Refined_Global => TokenPresence;

   ------------------------------------------------------------------
   -- ReadAndCheckAuthCert
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure ReadAndCheckAuthCert (AuthCertOK :    out Boolean)
     with Refined_Global  => (Input  => (Clock.CurrentTime,
                                         Clock.Now,
                                         ConfigData.State,
                                         Interfac.Input,
                                         Interfac.State,
                                         KeyStore.State,
                                         KeyStore.Store),
                              Output => (AuthCert,
                                         IDCert,
                                         TokenTry),
                              In_Out => (AuditLog.FileState,
                                         AuditLog.State,
                                         Interfac.Status,
                                         TokenID)),
          Refined_Depends => ((AuditLog.FileState,
                               AuditLog.State)     => (AuditLog.FileState,
                                                       AuditLog.State,
                                                       Clock.Now,
                                                       ConfigData.State,
                                                       Interfac.Input,
                                                       Interfac.State,
                                                       Interfac.Status,
                                                       KeyStore.Store),
                              (AuthCert,
                               AuthCertOK)         => (Clock.CurrentTime,
                                                       Interfac.Input,
                                                       Interfac.State,
                                                       Interfac.Status,
                                                       KeyStore.State,
                                                       KeyStore.Store),
                              IDCert               => (Interfac.Input,
                                                       Interfac.State,
                                                       Interfac.Status,
                                                       KeyStore.Store),
                              (Interfac.Status,
                               TokenID)            =>+ Interfac.State,
                              TokenTry             => Interfac.State)
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
        with Global  => (Input  => (Clock.Now,
                                    ConfigData.State,
                                    Interfac.Input,
                                    Interfac.State,
                                    KeyStore.Store,
                                    TokenID),
                         Output => IDCert,
                         In_Out => (AuditLog.FileState,
                                    AuditLog.State,
                                    Interfac.Status)),
             Depends => ((AuditLog.FileState,
                          AuditLog.State)     => (AuditLog.FileState,
                                                  AuditLog.State,
                                                  Clock.Now,
                                                  ConfigData.State,
                                                  Interfac.Input,
                                                  Interfac.State,
                                                  Interfac.Status,
                                                  KeyStore.Store),
                         IDCert               => (Interfac.Input,
                                                  Interfac.State,
                                                  Interfac.Status,
                                                  KeyStore.Store,
                                                  TokenID),
                         Interfac.Status      =>+ null)
      is
         RawCert        : CertTypes.RawCertificateT;

         CertFound      : Boolean;
         IDValid        : Boolean;
         IDStatus       : CertificateStatus;
         ExtractOK,
         Verified,
         TokenIDMatches : Boolean := False;

         IDCertContents : Cert.ID.ContentsT;

      begin
         Cert.ID.Clear(IDCertContents);

         Interfac.GetCertificate
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
                    TokenTypes.TokenIDT
                    (Cert.TheID
                       (Contents =>
                          Cert.ID.Cert_Id_To_Cert
                          (IDCertContents)).SerialNumber));

               Cert.IsOK
                 (RawCert    => RawCert,
                  Contents   => Cert.ID.Cert_ID_To_Cert (IDCertContents),
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

         IDCert := ValidIDCertT'(Valid    => IDValid,
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
        with Global  => (Input  => (Clock.CurrentTime,
                                    Clock.Now, ConfigData.State,
                                    IDCert, Interfac.Input,
                                    Interfac.State,
                                    KeyStore.State,
                                    KeyStore.Store),
                         Output => AuthValid,
                         In_Out => (AuditLog.FileState,
                                    AuditLog.State,
                                    AuthCertContents,
                                    Interfac.Status)),
             Depends => ((AuditLog.FileState,
                          AuditLog.State)     => (AuditLog.FileState,
                                                  AuditLog.State,
                                                  Clock.Now,
                                                  ConfigData.State,
                                                  Interfac.Input,
                                                  Interfac.State,
                                                  Interfac.Status,
                                                  KeyStore.Store),
                         AuthCertContents     =>+ (Interfac.Input,
                                                   Interfac.State,
                                                   Interfac.Status),
                         AuthValid            => (Clock.CurrentTime,
                                                  IDCert,
                                                  Interfac.Input,
                                                  Interfac.State,
                                                  Interfac.Status,
                                                  KeyStore.State,
                                                  KeyStore.Store),
                         Interfac.Status      =>+ null)
      is
         RawCert       : CertTypes.RawCertificateT;

         CertFound     : Boolean;
         ExtractOK,
         Verified,
         Current,
         BaseIDMatches : Boolean := False;

      begin
         Interfac.GetCertificate
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
                 (Cert.TheID
                   (Contents => Cert.ID.Cert_ID_To_Cert (IDCert.Contents)) =
                    Cert.Attr.TheBaseCert
                    (Contents => Cert.Attr.Auth.Cert_Attr_Auth_To_Cert_Attr
                       (AuthCertContents)));

               Cert.Attr.Auth.IsOK
                 (RawCert    => RawCert,
                  Contents   => AuthCertContents,
                  IsVerified => Verified);

               Current := Cert.IsCurrent
                 (Contents => Cert.Attr.Auth.Cert_Attr_Auth_To_Cert
                    (AuthCertContents));

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

      TokenTry := Interfac.TheTokenTry;

      Cert.Attr.Auth.Clear(Contents => AuthCertContents);

      if TokenTry = TokenTypes.GoodToken then
         TokenID  := Interfac.TheTokenID;

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
     with Refined_Global  => (Input  => (Clock.CurrentTime,
                                         Clock.Now,
                                         ConfigData.State,
                                         Interfac.Input,
                                         Interfac.State,
                                         KeyStore.Store,
                                         TokenTry),
                              Output => (IandACert,
                                         PrivCert),
                              In_Out => (AuditLog.FileState,
                                         AuditLog.State,
                                         IDCert,
                                         Interfac.Status)),
          Refined_Depends => ((AuditLog.FileState,
                               AuditLog.State)     => (AuditLog.FileState,
                                                       AuditLog.State,
                                                       Clock.Now,
                                                       ConfigData.State,
                                                       Interfac.Input,
                                                       Interfac.State,
                                                       Interfac.Status,
                                                       KeyStore.Store,
                                                       TokenTry),
                              (Description,
                               IandACert,
                               PrivCert,
                               TokenOK)            => (Clock.CurrentTime,
                                                       IDCert,
                                                       Interfac.Input,
                                                       Interfac.State,
                                                       Interfac.Status,
                                                       KeyStore.Store,
                                                       TokenTry),
                              IDCert               =>+ (Clock.CurrentTime,
                                                        TokenTry),
                              Interfac.Status      =>+ TokenTry)
   is
      IandACertContents     : Cert.Attr.IandA.ContentsT;
      PrivCertContents      : Cert.Attr.Priv.ContentsT;
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
      function MakeDescription (Text : in CommonTypes.StringF1)
                               return AuditTypes.DescriptionT
      is
         Result : AuditTypes.DescriptionT := AuditTypes.NoDescription;
      begin
         if Text'Last < Result'Last then
            Result (1 .. Text'Last) := Text;
         else
            Result := Text (1 .. Result'Last);
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
        with Global  => (Input  => Clock.CurrentTime,
                         Output => Description,
                         In_Out => IDCert),
             Depends => ((Description,
                          IDCert)      => (Clock.CurrentTime,
                                           IDCert))
      is
         Current        : Boolean;
         IDCertContents : Cert.ID.ContentsT;
      begin
         if IDCert.Valid then

            IDCertContents := IDCert.Contents;
            Current := Cert.IsCurrent
              (Contents => Cert.ID.Cert_ID_To_Cert (IDCertContents));

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
        with Global  => (Input  => (Clock.CurrentTime,
                                    Clock.Now,
                                    ConfigData.State,
                                    IDCert,
                                    Interfac.Input,
                                    Interfac.State,
                                    KeyStore.Store),
                         Output => PrivValid,
                         In_Out => (AuditLog.FileState,
                                    AuditLog.State,
                                    Description,
                                    Interfac.Status,
                                    PrivCertContents)),
             Depends => ((AuditLog.FileState,
                          AuditLog.State)     => (AuditLog.FileState,
                                                  AuditLog.State,
                                                  Clock.Now,
                                                  ConfigData.State,
                                                  Interfac.Input,
                                                  Interfac.State,
                                                  Interfac.Status,
                                                  KeyStore.Store),
                         Description          =>+ (Clock.CurrentTime,
                                                   IDCert,
                                                   Interfac.Input,
                                                   Interfac.State,
                                                   Interfac.Status,
                                                   KeyStore.Store),
                         Interfac.Status      =>+ null,
                         PrivCertContents     =>+ (Interfac.Input,
                                                   Interfac.State,
                                                   Interfac.Status),
                         PrivValid            => (Clock.CurrentTime,
                                                  IDCert,
                                                  Interfac.Input,
                                                  Interfac.State,
                                                  Interfac.Status,
                                                  KeyStore.Store))
      is
         RawCert         : CertTypes.RawCertificateT;
         IDCertContents  : Cert.ID.ContentsT;

         CertFound       : Boolean;
         ExtractOK,
           Verified,
           Current,
           BaseIDMatches : Boolean := False;
      begin
         Interfac.GetCertificate
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
                 (Cert.TheID
                   (Contents => Cert.ID.Cert_ID_To_Cert (IDCertContents)) =
                    Cert.Attr.TheBaseCert
                    (Contents => Cert.Attr.Priv.Cert_Attr_Priv_To_Cert_Attr
                    (PrivCertContents)));

               Cert.IsOK
                 (RawCert    => RawCert,
                  Contents   => Cert.Attr.Priv.Cert_Attr_Priv_To_Cert
                    (PrivCertContents),
                  IsVerified => Verified);

               Current := Cert.IsCurrent
                 (Cert.Attr.Priv.Cert_Attr_Priv_To_Cert (PrivCertContents));
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
        with Global  => (Input  => (Clock.CurrentTime,
                                    Clock.Now,
                                    ConfigData.State,
                                    IDCert,
                                    Interfac.Input,
                                    Interfac.State,
                                    KeyStore.Store),
                         Output => IandAValid,
                         In_Out => (AuditLog.FileState,
                                    AuditLog.State,
                                    Description,
                                    IandACertContents,
                                    Interfac.Status)),
             Depends => ((AuditLog.FileState,
                          AuditLog.State)     => (AuditLog.FileState,
                                                  AuditLog.State,
                                                  Clock.Now,
                                                  ConfigData.State,
                                                  Interfac.Input,
                                                  Interfac.State,
                                                  Interfac.Status,
                                                  KeyStore.Store),
                         Description          =>+ (Clock.CurrentTime,
                                                   IDCert,
                                                   Interfac.Input,
                                                   Interfac.State,
                                                   Interfac.Status,
                                                   KeyStore.Store),
                         IandACertContents    =>+ (Interfac.Input,
                                                   Interfac.State,
                                                   Interfac.Status),
                         IandAValid           => (Clock.CurrentTime,
                                                  IDCert,
                                                  Interfac.Input,
                                                  Interfac.State,
                                                  Interfac.Status,
                                                  KeyStore.Store),
                         Interfac.Status      =>+ null)
      is
         RawCert         : CertTypes.RawCertificateT;
         IDCertContents  : Cert.ID.ContentsT;

         CertFound       : Boolean;
         ExtractOK,
           Verified,
           Current,
           BaseIDMatches : Boolean := False;
      begin
         Interfac.GetCertificate
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
                 (Cert.TheID
                   (Contents => Cert.ID.Cert_ID_To_Cert (IDCertContents)) =
                  Cert.Attr.TheBaseCert
                    (Contents => Cert.Attr.IandA.Cert_Attr_IandA_To_Cert_Attr
                       (IandACertContents)));

               Cert.IsOK
                 (RawCert    => RawCert,
                  Contents   => Cert.Attr.IandA.Cert_Attr_IandA_To_Cert
                    (IandACertContents),
                  IsVerified => Verified);

               Current := Cert.IsCurrent
                 (Contents => Cert.Attr.IandA.Cert_Attr_IandA_To_Cert
                    (IandACertContents));


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
   procedure AddAuthCert (Success : out Boolean)
     with Refined_Global  => (Input  => (CertificateStore.State,
                                         Clock.CurrentTime,
                                         Clock.Now,
                                         ConfigData.State,
                                         IDCert,
                                         KeyStore.State,
                                         PrivCert),
                              Output => AuthCert,
                              In_Out => (AuditLog.FileState,
                                         AuditLog.State)),
          Refined_Depends => ((AuditLog.FileState,
                               AuditLog.State)     => (AuditLog.FileState,
                                                       AuditLog.State,
                                                       CertificateStore.State,
                                                       Clock.Now,
                                                       ConfigData.State),
                              AuthCert             => (CertificateStore.State,
                                                       Clock.CurrentTime,
                                                       ConfigData.State,
                                                       IDCert,
                                                       KeyStore.State,
                                                       PrivCert),
                              Success              => CertificateStore.State)--  ,
           --  Refined_Pre     => KeyStore.PrivateKeyPresent
   is
      ID               : CertTypes.IDT;
      NotBefore        : Clock.TimeT;
      NotAfter         : Clock.TimeT;
      Clearance        : PrivTypes.ClearanceT;

      IDCertContents   : Cert.ID.ContentsT;
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
           (ElementID   => AuditTypes.SystemFault,
            Severity    => AuditTypes.Warning,
            User        => AuditTypes.NoUser,
            Description => "No Serial Numbers avaiable for issue of Authorisation Certificate"
            );
         Success := False;
      end if;

      IDCertContents := IDCert.Contents;
      Cert.Attr.Auth.SetContents
        (ID         => ID,
         NotBefore  => NotBefore,
         NotAfter   => NotAfter,
         Mechanism  => CryptoTypes.SHA1_RSA,
         BaseCertID => Cert.TheID(Cert.ID.Cert_ID_To_Cert (IDCertContents)),
         Role       => Cert.Attr.Priv.TheRole(PrivCert.Contents),
         Clearance  => Clearance,
         Contents   => AuthCertContents);

      AuthCert := ValidAuthCertT'(Valid    => True,
                                  Contents => AuthCertContents);
   end AddAuthCert;

   ------------------------------------------------------------------
   -- GetIandATemplate
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   function GetIandATemplate return IandATypes.TemplateT is
     (Cert.Attr.IandA.TheTemplate(IandACert.Contents))
     with Refined_Global => IandACert;

   ------------------------------------------------------------------
   -- GetClass
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   function GetClass return PrivTypes.ClassT is
     (Cert.Attr.Auth.TheClearance(AuthCert.Contents).Class)
     with Refined_Global => AuthCert;

end UserToken;
