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

with Cert.ID,
     CertTypes,
     CommonTypes,
     CryptoTypes,
     KeyStore,
     AuditLog,
     Clock;

use type Clock.DurationT;
use type CryptoTypes.IssuerIDT;

package body Enrolment is

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
      function MakeDescription (Detail : in CommonTypes.StringF1L1000)
                                return AuditTypes.DescriptionT
        with Global => CertNo
      is
         Result  : AuditTypes.DescriptionT := AuditTypes.NoDescription;
         TheDesc : constant String :=
                               "Enrolment failed at certificate" &
                               CommonTypes.Integer_Image(CertNo) & " - " &
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
        with Global  => (Input  => (CertNo,
                                    Clock.Now,
                                    ConfigData.State),
                         In_Out => (AuditLog.FileState,
                                    AuditLog.State,
                                    KeyStore.State,
                                    KeyStore.Store,
                                    TheFile)),
             Depends => ((AuditLog.FileState,
                          AuditLog.State)     => (AuditLog.FileState,
                                                  AuditLog.State,
                                                  Clock.Now,
                                                  ConfigData.State,
                                                  IsTIS,
                                                  KeyStore.Store,
                                                  TheFile),
                         Description          => (CertNo,
                                                  IsTIS,
                                                  KeyStore.Store,
                                                  TheFile),
                         (KeyAdded,
                          KeyStore.Store)     => (IsTIS,
                                                  KeyStore.Store,
                                                  TheFile),
                         KeyStore.State       =>+ (IsTIS,
                                                   KeyStore.Store,
                                                   TheFile),
                         TheFile              =>+ null),
             Post    => (if IsTIS and KeyAdded then
                            KeyStore.PrivateKeyPresent) and
                         (if (not (IsTIS and KeyAdded)) then
                            (KeyStore.PrivateKeyPresent =
                               KeyStore.PrivateKeyPresent'Old))
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
            File.GetLine(TheFile, TheCert, Stop);
         end loop;

         Cert.ID.Extract
           (RawCert  => TheCert,
            Contents => TheContents,
            Success  => Extracted);

         TheSubject   := Cert.ID.TheSubject(TheContents);
         TheIssuer    := Cert.TheIssuer(Cert.ID.Cert_Id_To_Cert(TheContents));
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

         if Extracted and AddedOK then

            Cert.IsOK
              (RawCert => TheCert,
               Contents => Cert.ID.Cert_Id_To_Cert(TheContents),
               IsVerified => VerifiedOK);

         end if;

         if VerifiedOK and TheSubject.ID /= TheIssuer.ID then
            KeyStore.AddKey(TheOwner => TheSubject,
                            TheKey   => ThePublicKey,
                            IsPublic => True,
                            Added    => AddedOK);
         end if;

         -- If this is the TIS, add a private key as well.
         if VerifiedOK and AddedOK and IsTIS then
            KeyStore.AddKey(TheOwner => TheSubject,
                            TheKey   => ThePublicKey,
                            IsPublic => False,
                            Added    => AddedOK);
         end if;

         if not Extracted then
            Description :=
              MakeDescription("Certificate contents could not be extracted");
         elsif not AddedOK then
            Description :=
              MakeDescription("Key could not be added to the Key Store");
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
         pragma Loop_Invariant (KeyStore.PrivateKeyPresent);
         pragma Loop_Invariant (CertNo >= 2);

         if not File.EndOfLine(TheFile) then
            CertNo := CertNo + 1;
            pragma Annotate (GNATprove, False_Positive,
                             "overflow check might fail",
                             "This follows from the memory size of a floppy and the size of each certificate (in the region of 2**10 characters)");
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
