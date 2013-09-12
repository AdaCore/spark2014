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
-- AdminToken
--
-- Implementation Notes:
--    None.
--
------------------------------------------------------------------

with BasicTypes;
use type BasicTypes.PresenceT;

with TokenTypes;
use type TokenTypes.TryT;
use type TokenTypes.TokenIDT;

with CertTypes;
use type CertTypes.IDT;

with Cert.Attr.Auth;
use Cert.Attr.Auth;
with Cert.ID;
with AdminToken.Interfac;
with Clock;
with ConfigData;

package body AdminToken
--# own State  is TokenPresence,
--#               TokenTry,
--#               TokenID,
--#               AuthCert,
--#               IDCert,
--#               AdminToken.Interfac.State &
--#     Status is AdminToken.Interfac.Status &
--#     Input  is in AdminToken.Interfac.Input;
is
   pragma SPARK_Mode (Off);  --  tagged types
   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   type ValidAuthCertT is record
      Valid : Boolean;
      Contents : Cert.Attr.Auth.ContentsT;
   end record;

   type ValidIDCertT is record
      Valid : Boolean;
      Contents : Cert.ID.ContentsT;
   end record;

   ------------------------------------------------------------------
   -- State
   --
   ------------------------------------------------------------------
   TokenPresence : BasicTypes.PresenceT;

   TokenTry  : TokenTypes.TryT;

   TokenID   : TokenTypes.TokenIDT;

   AuthCert  : ValidAuthCertT;
   IDCert    : ValidIDCertT;

   function TheAuthCertRole return PrivTypes.PrivilegeT is
   begin
      return TheRole (AuthCert.Contents);
   end TheAuthCertRole;

   function IsGood return Boolean is
   begin
      return IDCert.Valid;
   end IsGood;

   function AuthCertValid return Boolean is
   begin
      return AuthCert.Valid;
   end AuthCertValid;

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
   --# global out TokenPresence;
   --#        out TokenTry;
   --#        out TokenID;
   --#        out AuthCert;
   --#        out IDCert;
   --# derives TokenPresence,
   --#         TokenTry,
   --#         TokenID,
   --#         AuthCert,
   --#         IDCert        from ;
   is

      AuthCertContents : Cert.Attr.Auth.ContentsT;
      IDCertContents    : Cert.ID.ContentsT;

   begin
      TokenPresence := BasicTypes.Absent;
      TokenTry      := TokenTypes.NoToken;
      TokenID       := TokenTypes.TokenIDT'First;

      Cert.Attr.Auth.Clear(AuthCertContents);
      AuthCert := ValidAuthCertT'(Valid    => False,
                                  Contents => AuthCertContents);

      Cert.ID.Clear(IDCertContents);
      IDCert := ValidIDCertT'(Valid    => False,
                              Contents => IDCertContents);

   end Clear;

   ------------------------------------------------------------------
   -- Init
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------

   procedure Init
   --# global in out Interfac.Status;
   --#           out TokenPresence;
   --#           out TokenTry;
   --#           out TokenID;
   --#           out AuthCert;
   --#           out IDCert;
   --#           out Interfac.State;
   --# derives TokenPresence,
   --#         TokenTry,
   --#         TokenID,
   --#         AuthCert,
   --#         IDCert           from  &
   --#         Interfac.Status,
   --#         Interfac.State  from Interfac.Status;
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
   --# global in     Interfac.Input;
   --#        in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in out Interfac.Status;
   --#        in out Interfac.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#           out TokenPresence;
   --# derives TokenPresence,
   --#         Interfac.State    from Interfac.Status,
   --#                                 Interfac.State,
   --#                                 Interfac.Input &
   --#         Interfac.Status   from * &
   --#         AuditLog.State,
   --#         AuditLog.FileState from *,
   --#                                 Interfac.Status,
   --#                                 Interfac.State,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 ConfigData.State,
   --#                                 Clock.Now;
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
     (Description :    out AuditTypes.DescriptionT;
      TokenOK     :    out Boolean)
   --# global in     Interfac.State;
   --#        in     Interfac.Input;
   --#        in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in     KeyStore.Store;
   --#        in     Clock.CurrentTime;
   --#        in     KeyStore.State;
   --#        in out TokenID;
   --#        in out Interfac.Status;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#           out TokenTry;
   --#           out AuthCert;
   --#           out IDCert;
   --# derives TokenID,
   --#         Interfac.Status   from *,
   --#                                 Interfac.State &
   --#         AuthCert,
   --#         TokenOK,
   --#         Description        from Interfac.Status,
   --#                                 Interfac.State,
   --#                                 Interfac.Input,
   --#                                 KeyStore.Store,
   --#                                 Clock.CurrentTime,
   --#                                 KeyStore.State &
   --#         AuditLog.State,
   --#         AuditLog.FileState from Interfac.Status,
   --#                                 Interfac.State,
   --#                                 Interfac.Input,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 ConfigData.State,
   --#                                 Clock.Now,
   --#                                 KeyStore.Store &
   --#         TokenTry           from Interfac.State &
   --#         IDCert             from Interfac.Status,
   --#                                 Interfac.State,
   --#                                 Interfac.Input,
   --#                                 KeyStore.Store;
   --# post TokenOk <-> ( IDCert.Valid and AuthCert.Valid and
   --#                    Cert.Attr.Auth.TheRole(AuthCert.Contents) in
   --#                        PrivTypes.AdminPrivilegeT );
   is
      pragma Postcondition
        (TokenOk =
           (IDCert.Valid and then
            AuthCert.Valid and then
            Cert.Attr.Auth.TheRole(AuthCert.Contents) in
              PrivTypes.AdminPrivilegeT));
      AuthValid, IDValid, RoleOK : Boolean;

      AuthCertContents : Cert.Attr.Auth.ContentsT;
      IDCertContents : Cert.ID.ContentsT;

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
     --#        in     Interfac.State;
     --#        in     Interfac.Input;
     --#        in     ConfigData.State;
     --#        in     Clock.Now;
     --#        in     KeyStore.Store;
     --#        in out Interfac.Status;
     --#        in out AuditLog.State;
     --#        in out AuditLog.FileState;
     --#        in out IDCertContents;
     --#           out Description;
     --#           out IDValid;
     --# derives AuditLog.State,
     --#         AuditLog.FileState from Interfac.Status,
     --#                                 Interfac.State,
     --#                                 Interfac.Input,
     --#                                 AuditLog.State,
     --#                                 AuditLog.FileState,
     --#                                 ConfigData.State,
     --#                                 Clock.Now,
     --#                                 KeyStore.Store &
     --#         Description,
     --#         IDValid            from TokenID,
     --#                                 Interfac.Status,
     --#                                 Interfac.State,
     --#                                 Interfac.Input,
     --#                                 KeyStore.Store &
     --#         Interfac.Status   from * &
     --#         IDCertContents     from *,
     --#                                 Interfac.Status,
     --#                                 Interfac.State,
     --#                                 Interfac.Input;
   is
      RawCert   : CertTypes.RawCertificateT;

      CertFound : Boolean;
      ExtractOK,
        Verified,
        TokenIDMatches : Boolean := False;

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
            Description := MakeDescription("ID Certificate Bad");
         elsif not Verified then
            Description :=
              MakeDescription("ID Certificate Not Verifiable");
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
        --# global in     Interfac.State;
        --#        in     Interfac.Input;
        --#        in     ConfigData.State;
        --#        in     Clock.Now;
        --#        in     KeyStore.Store;
        --#        in     Clock.CurrentTime;
        --#        in     KeyStore.State;
        --#        in     IDCertContents;
        --#        in out Interfac.Status;
        --#        in out AuditLog.State;
        --#        in out AuditLog.FileState;
        --#        in out Description;
        --#        in out AuthCertContents;
        --#           out AuthValid;
        --# derives AuditLog.State,
        --#         AuditLog.FileState from Interfac.Status,
        --#                                 Interfac.State,
        --#                                 Interfac.Input,
        --#                                 AuditLog.State,
        --#                                 AuditLog.FileState,
        --#                                 ConfigData.State,
        --#                                 Clock.Now,
        --#                                 KeyStore.Store &
        --#         Interfac.Status   from * &
        --#         Description        from *,
        --#                                 Interfac.Status,
        --#                                 Interfac.State,
        --#                                 Interfac.Input,
        --#                                 KeyStore.Store,
        --#                                 Clock.CurrentTime,
        --#                                 KeyStore.State,
        --#                                 IDCertContents &
        --#         AuthValid          from Interfac.Status,
        --#                                 Interfac.State,
        --#                                 Interfac.Input,
        --#                                 KeyStore.Store,
        --#                                 Clock.CurrentTime,
        --#                                 KeyStore.State,
        --#                                 IDCertContents &
        --#         AuthCertContents   from *,
        --#                                 Interfac.Status,
        --#                                 Interfac.State,
        --#                                 Interfac.Input;
      is
         RawCert : CertTypes.RawCertificateT;

         CertFound : Boolean;
         ExtractOK,
           Verified,
           Current,
           BaseIDMatches : Boolean := False;

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
                 (Cert.ID.TheID(Contents => IDCertContents) =
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

         if Description = AuditTypes.NoDescription then
            if not CertFound or not ExtractOK
              or not BaseIDMatches then
               Description := MakeDescription("Authorisation Certificate Bad");
            elsif not Verified then
               Description :=
                  MakeDescription("Authorisation Certificate Not Verifiable");
            elsif not Current then
               Description :=
                  MakeDescription("Authorisation Certificate Not Current");
            end if;
         end if;

      end CheckAuthCert;


   -----------------------------------------------------------------
   -- begin ReadAndCheck
   -----------------------------------------------------------------
   begin

      TokenTry := Interfac.TheTokenTry;

      Cert.Attr.Auth.Clear(Contents => AuthCertContents);
      Cert.ID.Clear(Contents => IDCertContents);

      if TokenTry = TokenTypes.GoodToken then
         TokenID  := Interfac.TheTokenID;

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
         Description := MakeDescription("Token Bad");

      end if;

      TokenOK := AuthValid and IDValid and RoleOK;

      IDCert := ValidIDCertT'( Valid    => IDValid,
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
   function IsPresent return Boolean
   --# global TokenPresence;
   is
   begin
      return TokenPresence = BasicTypes.Present;
   end IsPresent;

   ------------------------------------------------------------------
   -- IsCurrent
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   function IsCurrent return Boolean
   --# global AuthCert,
   --#        Clock.CurrentTime;
   is
   begin
      return Cert.Attr.Auth.IsCurrent(Contents => AuthCert.Contents);
   end IsCurrent;


   ------------------------------------------------------------------
   -- ExtractUser
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   function ExtractUser return AuditTypes.UserTextT
   --# global TokenTry,
   --#        AuthCert,
   --#        IDCert;
   is
      Result : AuditTypes.UserTextT;
   begin
      if TokenTry = TokenTypes.GoodToken then
         if IDCert.Valid then
            Result := Cert.ID.ExtractUser(IDCert.Contents);
         elsif AuthCert.Valid then
            Result := Cert.Attr.Auth.ExtractUser(AuthCert.Contents);
         else
            Result := AuditTypes.NoUser;
         end if;
      else
         Result := AuditTypes.NoUser;
      end if;
      return Result;
   end ExtractUser;

   ------------------------------------------------------------------
   -- GetRole
   --
   -- Description:
   --    obtains the role value for the Auth certificate.
   --
   -- Traceunit : C.AdminToken.GetRole
   -- Traceto :
   ------------------------------------------------------------------
   function GetRole return PrivTypes.AdminPrivilegeT
   --# global AuthCert;
   --# pre Cert.Attr.Auth.TheRole(AuthCert.Contents) in
   --#           PrivTypes.AdminPrivilegeT;
   is
      pragma Precondition (Cert.Attr.Auth.TheRole(AuthCert.Contents) in
                             PrivTypes.AdminPrivilegeT);
   begin
      return Cert.Attr.Auth.TheRole(Contents => AuthCert.Contents);
   end GetRole;

end AdminToken;
