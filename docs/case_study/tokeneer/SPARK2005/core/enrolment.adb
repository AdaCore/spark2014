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
-- Enrolment
--
-- Implementation Notes:
--    None.
--
------------------------------------------------------------------

with Cert.ID;
with CertTypes;
with CryptoTypes;
with KeyStore;
with AuditLog;
with Clock;

use type Clock.DurationT;
use type CryptoTypes.IssuerIDT;

package body Enrolment
is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------


   ------------------------------------------------------------------
   -- Validate
   --
   -- Implementation Notes:
   --      None.
   ------------------------------------------------------------------
   procedure Validate (TheFile     : in out File.T;
                       DataOK      :    out Boolean;
                       Description :    out AuditTypes.DescriptionT)
   is
      CertNo   : Positive := 1;
      ClosedOK : Boolean;

      ------------------------------------------------------------------
      -- MakeDescription
      --
      -- Description:
      --    Constructs an enrolment failure description, adding the imported
      --    Detail to the text. The description will be truncated if required.
      --
      -- Implementation Notes:
      --    Hidden from SPARK because of use of slicing.
      ------------------------------------------------------------------
      function MakeDescription (Detail : in String)
                                return AuditTypes.DescriptionT
      --# global CertNo;
      is
         --# hide MakeDescription;
         Result  : AuditTypes.DescriptionT := AuditTypes.NoDescription;
         TheDesc : constant String :=
                               "Enrolment failed at certificate" &
                               Positive'Image(CertNo) & " - " &
                               Detail;
      begin
         if TheDesc'Last < Result'Last then
            Result( 1 .. TheDesc'Last) := TheDesc;
         else
            Result := TheDesc( 1 .. Result'Last);
         end if;
         return Result;

      end MakeDescription;


      ------------------------------------------------------------------
      -- ValidateAndAddKey
      --
      -- Description:
      --    Validates that the key has come from a trusted source, and
      --    if so adds the key to the Store. If a validation failure
      --    occurs then this information is exported, in order to
      --    create an audit entry.
      --
      -- Implementation Notes:
      --    None
      --
      ------------------------------------------------------------------
      procedure ValidateAndAddKey(IsTIS       : in     Boolean;
                                  KeyAdded    :    out Boolean;
                                  Description :    out AuditTypes.DescriptionT)
      --# global in     CertNo;
      --#        in     ConfigData.State;
      --#        in     Clock.Now;
      --#        in out KeyStore.Store;
      --#        in out TheFile;
      --#        in out AuditLog.State;
      --#        in out AuditLog.FileState;
      --#        in out KeyStore.State;
      --# derives KeyAdded,
      --#         KeyStore.Store     from KeyStore.Store,
      --#                                 IsTIS,
      --#                                 TheFile &
      --#         AuditLog.State,
      --#         AuditLog.FileState from KeyStore.Store,
      --#                                 IsTIS,
      --#                                 TheFile,
      --#                                 AuditLog.State,
      --#                                 AuditLog.FileState,
      --#                                 ConfigData.State,
      --#                                 Clock.Now &
      --#         TheFile            from * &
      --#         Description        from CertNo,
      --#                                 KeyStore.Store,
      --#                                 IsTIS,
      --#                                 TheFile &
      --#         KeyStore.State     from *,
      --#                                 KeyStore.Store,
      --#                                 IsTIS,
      --#                                 TheFile;
      --# post ((IsTIS and KeyAdded) ->
      --#          KeyStore.PrivateKeyPresent(KeyStore.State)) and
      --#      (not (IsTIS and KeyAdded) ->
      --#          KeyStore.PrivateKeyPresent(KeyStore.State) =
      --#             KeyStore.PrivateKeyPresent(KeyStore.State~));
      is
         TheCert      : CertTypes.RawCertificateT :=
                           CertTypes.NullRawCertificate;
         TheContents  : Cert.ID.ContentsT;
         TheSubject,
         TheIssuer    : CryptoTypes.IssuerT;
         ThePublicKey : CryptoTypes.KeyPartT;

         Extracted   : Boolean;
         AddedOK     : Boolean := True;
         VerifiedOK  : Boolean := False;

         Stop        : Natural := 0;

      begin
         Description := AuditTypes.NoDescription;

         while Stop = 0 and not File.EndOfFile(TheFile) loop
            -- Read the next (non-empty) line of the enrolment file
            --# assert KeyStore.PrivateKeyPresent(KeyStore.State) =
            --#           KeyStore.PrivateKeyPresent(KeyStore.State~);
            File.GetLine(TheFile, TheCert, Stop);
         end loop;

         Cert.ID.Extract
           (RawCert  => TheCert,
            Contents => TheContents,
            Success  => Extracted);

         TheSubject   := Cert.ID.TheSubject(TheContents);
         TheIssuer    := Cert.ID.TheIssuer(TheContents);
         ThePublicKey := Cert.ID.ThePublicKey(TheContents);

         if Extracted then

            -- Is this a CA?
            if TheSubject.ID = TheIssuer.ID then

               -- If so, it is self-signed, so need to add the key
               -- to the keystore before verifying
               KeyStore.AddKey(TheOwner => TheSubject,
                               TheKey   => ThePublicKey,
                               IsPublic => True,
                               Added    => AddedOK);

            end if;
         end if;

         --# assert KeyStore.PrivateKeyPresent(KeyStore.State) =
         --#           KeyStore.PrivateKeyPresent(KeyStore.State~);

         if Extracted and AddedOK then

            Cert.ID.IsOK
              ( RawCert => TheCert,
                Contents => TheContents,
                IsVerified => VerifiedOK);

         end if;

         if VerifiedOK and TheSubject.ID /= TheIssuer.ID then
            KeyStore.AddKey(TheOwner => TheSubject,
                            TheKey   => ThePublicKey,
                            IsPublic => True,
                            Added    => AddedOK);
         end if;

         --# assert KeyStore.PrivateKeyPresent(KeyStore.State) =
         --#           KeyStore.PrivateKeyPresent(KeyStore.State~);

         -- If this is the TIS, add a private key as well.
         if VerifiedOK and AddedOK and IsTIS then
            KeyStore.AddKey(TheOwner => TheSubject,
                            TheKey   => ThePublicKey,
                            IsPublic => False,
                            Added    => AddedOK);
         end if;

         if not Extracted then
            Description := MakeDescription("Certificate contents could not be extracted");
         elsif not AddedOK then
            Description := MakeDescription("Key could not be added to the Key Store");
         elsif not VerifiedOK then
            Description := MakeDescription("Certificate could not be verified");
         end if;

         KeyAdded := VerifiedOK and AddedOK;

      end ValidateAndAddKey;


   begin
      File.OpenRead (TheFile => TheFile,
                     Success => DataOK);

      if DataOK then
         -- The first Cert should be the TIS issuer.
         ValidateAndAddKey(IsTIS       => False,
                           KeyAdded    => DataOK,
                           Description => Description);
      else
         Description := MakeDescription("The enrolment file is corrupt");
      end if;

      if DataOK then
         -- Next Cert should be the TIS issuer.
         CertNo := CertNo + 1;
         ValidateAndAddKey(IsTIS       => True,
                           KeyAdded    => DataOK,
                           Description => Description);
      end if;

      -- Continue through the certificates until the end is
      -- reached, or certificate validation fails
      while not File.EndOfFile(TheFile) and DataOK loop
         --# assert KeyStore.PrivateKeyPresent(KeyStore.State) and
         --#        CertNo >= 2;

         if not File.EndOfLine(TheFile) then
         CertNo := CertNo + 1;
         ValidateAndAddKey(IsTIS       => False,
                           KeyAdded    => DataOK,
                           Description => Description);
         else
            File.SkipLine(TheFile, 1);
         end if;
      end loop;

      File.Close (TheFile => TheFile,
                  Success => ClosedOK);

      if not ClosedOK then
         Description := MakeDescription("The enrolment file is corrupt");
         DataOK := False;
      end if;

      if not DataOK then
         -- enrolment has failed - delete the keystore
         KeyStore.Delete;
      end if;

   end Validate;

end Enrolment;
