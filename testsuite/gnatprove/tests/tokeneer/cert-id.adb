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
-- Cert.ID
--
-- Implementation Notes:
--    None.
--
------------------------------------------------------------------
with CertProcessing;
with CommonTypes;
use type CommonTypes.Unsigned32T;
with Clock;

package body Cert.ID is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------

   ------------------------------------------------------------------
   -- TheSubject
   --
   --   Implementation Notes:
   --      None
   --
   ------------------------------------------------------------------
   function TheSubject (Contents : ContentsT) return CryptoTypes.IssuerT is
     (Contents.Subject);

   ------------------------------------------------------------------
   -- ThePublicKey
   --
   --   Implementation Notes:
   --      None
   --
   ------------------------------------------------------------------
   function ThePublicKey (Contents : ContentsT) return CryptoTypes.KeyPartT is
     (Contents.SubjectPublicKey);

   ------------------------------------------------------------------
   -- Extract
   --
   --   Implementation Notes:
   --      None.
   --
   ------------------------------------------------------------------
   procedure Extract (RawCert  : in     CertTypes.RawCertificateT;
                      Contents :    out ContentsT;
                      Success  :    out Boolean)
   is
      LocalContents : CertProcessing.IDCertDataT;
      Extracted,
      KeyLengthOK,
      NotBeforeOk,
      NotAfterOk    : Boolean;
   begin
      CertProcessing.ExtractIDCertData(RawIDCert      => RawCert,
                                       IDCert         => LocalContents,
                                       ExtractSuccess => Extracted);

      Contents.ID.Issuer        := LocalContents.Issuer;
      Contents.ID.SerialNumber  :=
        CertTypes.SerialNumberT(LocalContents.SerialNumber);
      Contents.Mechanism        := LocalContents.SigAlgID;
      Contents.Subject          := LocalContents.Subject;

      Contents.SubjectPublicKey.AlgorithmID :=
        LocalContents.SubjectPublicKeyInfo.AlgorithmId;
      Contents.SubjectPublicKey.KeyID :=
        CryptoTypes.KeyIDT(LocalContents.SubjectPublicKeyInfo.KeyID);
      if LocalContents.SubjectPublicKeyInfo.KeyLength >=
        CommonTypes.Unsigned32T(CryptoTypes.KeyLengthT'First)
        and LocalContents.SubjectPublicKeyInfo.KeyLength <=
        CommonTypes.Unsigned32T(CryptoTypes.KeyLengthT'Last)
      then
         Contents.SubjectPublicKey.KeyLength := CryptoTypes.KeyLengthT
           (LocalContents.SubjectPublicKeyInfo.KeyLength);
         KeyLengthOK := True;
      else
         Contents.SubjectPublicKey.KeyLength :=
           CryptoTypes.KeyLengthT'First;
         KeyLengthOK := False;
      end if;


      -- NotBefore and NotAfter are read as unsigned 32 bit words -
      -- convert to Clock.TimeT
      Clock.ConstructTime(
               Year    => LocalContents.Validity.NotBefore.Year,
               Month   => LocalContents.Validity.NotBefore.Month,
               Day     => LocalContents.Validity.NotBefore.Day,
               Hour    => LocalContents.Validity.NotBefore.Hour,
               Min     => LocalContents.Validity.NotBefore.Minute,
               TheTime => Contents.NotBefore,
               Success => NotBeforeOK);

      Clock.ConstructTime(
               Year    => LocalContents.Validity.NotAfter.Year,
               Month   => LocalContents.Validity.NotAfter.Month,
               Day     => LocalContents.Validity.NotAfter.Day,
               Hour    => LocalContents.Validity.NotAfter.Hour,
               Min     => LocalContents.Validity.NotAfter.Minute,
               TheTime => Contents.NotAfter,
               Success => NotAfterOK);

      Success := Extracted and NotBeforeOK and NotAfterOK and KeyLengthOK;
   end Extract;

   ------------------------------------------------------------------
   -- Clear
   --
   --   Implementation Notes:
   --      None
   --
   ------------------------------------------------------------------
   procedure Clear (Contents :    out ContentsT)
   is
   begin
      Contents := NullContents;
   end Clear;

   --  Converts the extended type to the original one.
   function Cert_Id_To_Cert (Contents : in ContentsT) return Cert.ContentsT is
     (Cert.ContentsT'(ID        => Contents.ID,
                      NotBefore => Contents.NotBefore,
                      NotAfter  => Contents.NotAfter,
                      Mechanism => Contents.Mechanism));
end Cert.ID;
