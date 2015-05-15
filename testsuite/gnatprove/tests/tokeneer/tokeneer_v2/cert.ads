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
-- Cert
--
-- Description:
--    Defines the common contents of a certificate, and operations on
--    those contents.Certificates enter the system as raw data, and
--    are stored in an internally-defined record structure.
--
------------------------------------------------------------------

with AuditLog,
     AuditTypes,
     CertTypes,
     Clock,
     ConfigData,
     CryptoTypes,
     Keystore;


package Cert is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------

   ------------------------------------------------------------------
   -- ContentsT
   --
   -- Description:
   --    Contents common to all certificates
   --
   -- Traceunit : C.Cert.Contents
   -- Traceto   : FD.Types.Certificates
   ------------------------------------------------------------------
   type ContentsT is private;


   ------------------------------------------------------------------
   -- TheIssuer
   --
   -- Description:
   --    Retrieves the issuer of the certificate
   --
   -- Traceunit : C.Cert.TheIssuer
   -- Traceto   : FD.Types.Certificates
   ------------------------------------------------------------------
   function TheIssuer (Contents : ContentsT) return CryptoTypes.IssuerT;

   ------------------------------------------------------------------
   -- TheID
   --
   -- Description:
   --    Retrieves the certificate ID (includes Issuer and serial number).
   --
   -- Traceunit : C.Cert.TheID
   -- Traceto   : FD.Types.Certificates
   ------------------------------------------------------------------
   function TheID (Contents : ContentsT) return CertTypes.IDT;

   ------------------------------------------------------------------
   -- ExtractUser
   --
   -- Description:
   --    Returns the user info as a string
   --
   -- Traceunit : C.Cert.ExtractUser
   -- Traceto   : FD.AuditLog.ExtractUser
   ------------------------------------------------------------------
   function ExtractUser (Contents : ContentsT) return AuditTypes.UserTextT;

   ------------------------------------------------------------------
   -- TheMechanism
   --
   -- Description:
   --    Retrieves the crypto mechanism
   --
   -- Traceunit : C.Cert.TheMechanism
   -- Traceto   : FD.Types.Certificates
   ------------------------------------------------------------------
   function TheMechanism (Contents : ContentsT) return CryptoTypes.AlgorithmT;

   ------------------------------------------------------------------
   -- IsCurrent
   --
   -- Description:
   --    Determines whether the certificate is current
   --
   -- Traceunit : C.Cert.IsCurrent
   -- Traceto   : FD.Certificate.IsCurrent
   ------------------------------------------------------------------
   function IsCurrent (Contents : ContentsT) return Boolean
     with Global => Clock.CurrentTime;

   ------------------------------------------------------------------
   -- GetData
   --
   -- Description:
   --    Retrieves the raw data contained in a raw certificate
   --
   -- Traceunit : C.Cert.GetData
   -- Traceto   : FD.Types.Certificates
   ------------------------------------------------------------------
   function GetData (RawCert : CertTypes.RawCertificateT)
                    return CertTypes.RawDataT
     with Global  => null;

   ------------------------------------------------------------------
   -- GetSignature
   --
   -- Description:
   --    Retrieves the signature contained in a raw certificate
   --
   -- Traceunit : C.Cert.GetSignature
   -- Traceto   : FD.Types.Certificates
   ------------------------------------------------------------------
   function GetSignature (RawCert : CertTypes.RawCertificateT)
                         return CertTypes.SignatureT;

   ------------------------------------------------------------------
   -- IssuerKnown
   --
   -- Description:
   --    Retrieves the issuer of the certificate
   --    May raise system faults.
   --
   -- Traceunit : C.Cert.IssuerKnown
   -- Traceto   : FD.Certificate.SignedOK
   ------------------------------------------------------------------
   procedure IssuerKnown (Contents : in     ContentsT;
                         IsKnown   :    out Boolean)
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State,
                                 KeyStore.Store),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Contents,
                                               KeyStore.Store),
                      IsKnown              => (Contents,
                                               KeyStore.Store));

   ------------------------------------------------------------------
   -- IsOK
   --
   -- Description:
   --    Determines whether the certificate is verified by a
   --    known issuer
   --
   -- Traceunit : C.Cert.IsOK
   -- Traceto   : FD.Certificate.SignedOK
   ------------------------------------------------------------------
   procedure IsOK (RawCert    : in     CertTypes.RawCertificateT;
                   Contents   : in     ContentsT;
                   IsVerified :    out Boolean)
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State,
                                 KeyStore.Store),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Contents,
                                               KeyStore.Store,
                                               RawCert),
                      IsVerified           => (Contents,
                                               KeyStore.Store,
                                               RawCert));

private
   type ContentsT is record
      ID        : CertTypes.IDT;
      NotBefore : Clock.TimeT;
      NotAfter  : Clock.TimeT;
      Mechanism : CryptoTypes.AlgorithmT;
   end record;

   NullContents : constant ContentsT :=
     ContentsT'(ID        => CertTypes.NullID,
                NotBefore => Clock.ZeroTime,
                NotAfter  => Clock.ZeroTime,
                Mechanism => CryptoTypes.AlgorithmT'First);
end Cert;
