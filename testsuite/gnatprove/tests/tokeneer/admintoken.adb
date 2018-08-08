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
-- AdminToken
--
-- Implementation Notes:
--    None.
--
------------------------------------------------------------------

with CertTypes;
use type CertTypes.IDT;

with AdminToken.Interfac;
with Clock;
with ConfigData;

package body AdminToken
  with Refined_State => (State  => (TokenPresence,
                                    TokenTry,
                                    TokenID,
                                    AuthCert,
                                    IDCert,
                                    AdminToken.Interfac.State),
                         Status => AdminToken.Interfac.Status,
                         Input  => AdminToken.Interfac.Input)
is
   ------------------------------------------------------------------
   -- Public Operations
   --
   ------------------------------------------------------------------

   ------------------------------------------------------------------
   -- Init
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure Init
     with Refined_Global  => (Output => (AuthCert,
                                         IDCert,
                                         Interfac.State,
                                         TokenID,
                                         TokenPresence,
                                         TokenTry),
                              In_Out => Interfac.Status),
          Refined_Depends => ((AuthCert,
                               IDCert,
                               TokenID,
                               TokenPresence,
                               TokenTry)        => null,
                              (Interfac.State,
                               Interfac.Status) => Interfac.Status)
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
     with Refined_Global  => (Proof_In => (AuthCert,
                                           IDCert),
                              Input    => (Clock.Now,
                                           ConfigData.State,
                                           Interfac.Input),
                              Output   => TokenPresence,
                              In_Out   => (AuditLog.FileState,
                                           AuditLog.State,
                                           Interfac.State,
                                           Interfac.Status)),
          Refined_Depends => ((AuditLog.FileState,
                               AuditLog.State)     => (AuditLog.FileState,
                                                       AuditLog.State,
                                                       Clock.Now,
                                                       ConfigData.State,
                                                       Interfac.State,
                                                       Interfac.Status),
                              (Interfac.State,
                               TokenPresence)      => (Interfac.Input,
                                                       Interfac.State,
                                                       Interfac.Status),
                              Interfac.Status      =>+ null)
   is
   begin
      Interfac.Poll;
      TokenPresence := Interfac.TheTokenPresence;
   end Poll;

   ------------------------------------------------------------------
   -- ReadAndCheck
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure ReadAndCheck
     (Description : out AuditTypes.DescriptionT;
      TokenOK     : out Boolean)
     with Refined_Global => (Input  => (Clock.CurrentTime,
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
                               AuditLog.State)        => (AuditLog.FileState,
                                                          AuditLog.State,
                                                          Clock.Now,
                                                          ConfigData.State,
                                                          Interfac.Input,
                                                          Interfac.State,
                                                          Interfac.Status,
                                                          KeyStore.Store),
                              (AuthCert, Description,
                               TokenOK)               => (Clock.CurrentTime,
                                                          Interfac.Input,
                                                          Interfac.State,
                                                          Interfac.Status,
                                                          KeyStore.State,
                                                          KeyStore.Store),
                              IDCert                  => (Interfac.Input,
                                                          Interfac.State,
                                                          Interfac.Status,
                                                          KeyStore.Store),
                              (Interfac.Status,
                               TokenID)               =>+ Interfac.State,
                              TokenTry                => Interfac.State),

          Refined_Post    => TokenOk = (IDCert.Valid and then
                                        AuthCert.Valid and then
                                        Cert.Attr.Auth.TheRole
                                          (AuthCert.Contents) in
                                          PrivTypes.AdminPrivilegeT)
   is
      AuthValid, IDValid, RoleOK : Boolean;

      AuthCertContents : Cert.Attr.Auth.ContentsT;
      IDCertContents   : Cert.ID.ContentsT;

      ------------------------------------------------------------------
      -- MakeDescription
      --
      -- Description:
      --    Constructs a description from a piece of text,
      --    truncating if required.
      --
      ------------------------------------------------------------------
      function MakeDescription (Text : in String)
                               return AuditTypes.DescriptionT
        with Pre => Text'First = 1
      is
         Result : AuditTypes.DescriptionT := AuditTypes.NoDescription;
      begin
         if Text'Last < Result'Last then
            Result (1 .. Text'Last) := Text;
         else
#if SECURITY_DEMO
            --  buffer overflow: wrong computation of bounds
            Result := Text (1 .. Text'Last);
#else
            Result := Text (1 .. Result'Last);
#end if;
         end if;

         return Result;
      end MakeDescription;

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
                         Output => (Description,
                                    IDValid),
                         In_Out => (AuditLog.FileState,
                                    AuditLog.State,
                                    IDCertContents,
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
                         (Description,
                          IDValid)            => (Interfac.Input,
                                                  Interfac.State,
                                                  Interfac.Status,
                                                  KeyStore.Store,
                                                  TokenID),
                         IDCertContents       =>+ (Interfac.Input,
                                                   Interfac.State,
                                                   Interfac.Status),
                         Interfac.Status      =>+ null)
      is
         RawCert   : CertTypes.RawCertificateT;

         CertFound : Boolean;
         ExtractOK, Verified, TokenIDMatches : Boolean := False;
      begin

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
                 (TokenID = TokenTypes.TokenIDT
                    (Cert.TheID (Contents => Cert.Id.Cert_Id_To_Cert
                                   (Contents => IDCertContents)).SerialNumber));

               Cert.IsOK
                 (RawCert => RawCert,
                  Contents => Cert.Id.Cert_Id_To_Cert
                    (Contents => IDCertContents),
                  IsVerified => Verified);

            end if;
         end if;

         IDValid := CertFound and ExtractOK
           and TokenIDMatches and Verified;

         if not CertFound or not ExtractOK or not TokenIDMatches then
            Description := MakeDescription ("ID Certificate Bad");
         elsif not Verified then
            Description :=
              MakeDescription ("ID Certificate Not Verifiable");
         else
            Description := AuditTypes.NoDescription;
         end if;

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
                                    Clock.Now,
                                    ConfigData.State,
                                    IDCertContents,
                                    Interfac.Input,
                                    Interfac.State,
                                    KeyStore.State,
                                    KeyStore.Store),
                         Output => AuthValid,
                         In_Out => (AuditLog.FileState,
                                    AuditLog.State,
                                    AuthCertContents,
                                    Description,
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
                                                  IDCertContents,
                                                  Interfac.Input,
                                                  Interfac.State,
                                                  Interfac.Status,
                                                  KeyStore.State,
                                                  KeyStore.Store),
                         Description          =>+ (Clock.CurrentTime,
                                                   IDCertContents,
                                                   Interfac.Input,
                                                   Interfac.State,
                                                   Interfac.Status,
                                                   KeyStore.State,
                                                   KeyStore.Store),
                         Interfac.Status      =>+ null)
      is
         RawCert : CertTypes.RawCertificateT;

         CertFound : Boolean;
         ExtractOK, Verified, Current, BaseIDMatches : Boolean := False;
      begin
         Interfac.GetCertificate
           (RawCert  => RawCert,
            CertType => CertTypes.AuthCert,
            Found    => CertFound);

         if CertFound then
            Cert.Attr.Auth.Extract
              (RawCert  => RawCert,
               Contents => AuthCertContents,
               Success  => ExtractOK);

            if ExtractOK then

               BaseIDMatches :=
                 (Cert.TheID(Contents => Cert.ID.Cert_Id_To_Cert
                               (Contents => IDCertContents)) =
                  Cert.Attr.TheBaseCert
                    (Contents =>  Cert.Attr.Auth.Cert_Attr_Auth_To_Cert_Attr
                       (AuthCertContents)));

               Cert.Attr.Auth.IsOK
                 (RawCert    => RawCert,
                  Contents   => AuthCertContents,
                  IsVerified => Verified);

               Current := Cert.IsCurrent
                 (Contents => Cert.Attr.Auth.Cert_Attr_Auth_To_Cert
                    (Contents => AuthCertContents));

            end if;

         end if;

         AuthValid := CertFound
                        and ExtractOK
                        and BaseIDMatches
                        and Verified
                        and Current;

         if Description = AuditTypes.NoDescription then
            if not CertFound
              or not ExtractOK
              or not BaseIDMatches
            then
               Description := MakeDescription ("Authorisation Certificate Bad");
            elsif not Verified then
               Description :=
                  MakeDescription ("Authorisation Certificate Not Verifiable");
            elsif not Current then
               Description :=
                  MakeDescription ("Authorisation Certificate Not Current");
            end if;
         end if;

      end CheckAuthCert;

   -----------------------------------------------------------------
   -- begin ReadAndCheck
   -----------------------------------------------------------------
   begin

      TokenTry := Interfac.TheTokenTry;

      Cert.Attr.Auth.Clear (Contents => AuthCertContents);
      Cert.ID.Clear (Contents => IDCertContents);

      if TokenTry = TokenTypes.GoodToken then
         TokenID := Interfac.TheTokenID;

         CheckIDCertOK;

         CheckAuthCert;

         -- Check the role on the auth certificate.
         if IDValid and AuthValid then
            if Cert.Attr.Auth.TheRole(Contents => AuthCertContents) in
              PrivTypes.AdminPrivilegeT then
               RoleOK := True;
            else
               Description := MakeDescription
                 ("Authorisation Certificate not for Administrator");
               RoleOK := False;
            end if;
         else
            RoleOK := False;
         end if;

      else
         AuthValid   := False;
         IDValid     := False;
         RoleOK      := False;
         Description := MakeDescription ("Token Bad");

      end if;

      TokenOK := AuthValid and IDValid and RoleOK;

      IDCert := ValidIDCertT'(Valid    => IDValid,
                               Contents => IDCertContents);

      AuthCert := ValidAuthCertT'
        (Valid    => AuthValid,
         Contents => AuthCertContents);

   end ReadAndCheck;

   ------------------------------------------------------------------
   -- IsPresent
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   function IsPresent return Boolean is
     (TokenPresence = CommonTypes.Present)
     with Refined_Global => TokenPresence;

   ------------------------------------------------------------------
   -- IsCurrent
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   function IsCurrent return Boolean is
     (Cert.IsCurrent (Contents => Cert_Attr_Auth_To_Cert
                        (Contents => AuthCert.Contents)))
     with Refined_Global => (AuthCert, Clock.CurrentTime);

   ------------------------------------------------------------------
   -- ExtractUser
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   function ExtractUser return AuditTypes.UserTextT
     with Refined_Global => (AuthCert,
                             IDCert,
                             TokenTry)
   is
      Result : AuditTypes.UserTextT;
   begin
      if TokenTry = TokenTypes.GoodToken then
         if IDCert.Valid then
            Result := Cert.ExtractUser (Cert.ID.Cert_Id_To_Cert
                                          (Contents => IDCert.Contents));
         elsif AuthCert.Valid then
            Result := Cert.ExtractUser (Cert.Attr.Auth.Cert_Attr_Auth_To_Cert
                                          (Contents => AuthCert.Contents));
         else
            Result := AuditTypes.NoUser;
         end if;
      else
         Result := AuditTypes.NoUser;
      end if;
      return Result;
   end ExtractUser;

   ------------------------------------------------------------------
   -- Clear
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure Clear
     with Refined_Global  => (Output => (AuthCert,
                                         IDCert,
                                         TokenID,
                                         TokenPresence,
                                         TokenTry)),
          Refined_Depends => ((AuthCert,
                               IDCert,
                               TokenID,
                               TokenPresence,
                               TokenTry)      => null)
   is
      AuthCertContents : Cert.Attr.Auth.ContentsT;
      IDCertContents   : Cert.ID.ContentsT;
   begin
      TokenPresence := CommonTypes.Absent;
      TokenTry      := TokenTypes.NoToken;
      TokenID       := TokenTypes.TokenIDT'First;

      Cert.Attr.Auth.Clear(AuthCertContents);
      AuthCert := ValidAuthCertT'(Valid    => False,
                                  Contents => AuthCertContents);

      Cert.ID.Clear(IDCertContents);
      IDCert := ValidIDCertT'(Valid    => False,
                              Contents => IDCertContents);

   end Clear;

end AdminToken;
