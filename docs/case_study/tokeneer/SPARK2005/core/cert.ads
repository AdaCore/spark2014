------------------------------------------------------------------
-- Tokeneer ID Station Core Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency. All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd. under contract to the National Security Agency.
--
-- Modifications to proof annotations by Phil Thornley, April 2009
------------------------------------------------------------------

------------------------------------------------------------------
-- Cert
--
-- Description:
--    Defines the common contents of a certificate, and operations on
--    those contents. Certificates enter the system as raw data, and
--    are stored in an internally-defined record structure.
--
------------------------------------------------------------------

with AuditTypes,
     CertTypes,
     Clock,
     CryptoTypes;

--# inherit AuditTypes,
--#         AuditLog,
--#         BasicTypes,
--#         ConfigData,
--#         CertProcessing,
--#         CertTypes,
--#         Clock,
--#         CryptoTypes,
--#         KeyStore;


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
   type ContentsT is tagged private;

   ------------------------------------------------------------------
   -- prf_idIssuer
   --
   -- Description:
   --    Proof functiom to model the C.ID.Issuer field of the record.
   --    Defined by the rule:
   --      prf_idissuer(C) may_be_replaced_by fld_issuer(fld_id(C)) .
   ------------------------------------------------------------------
   --# function prf_idIssuer (C : ContentsT) return CryptoTypes.IssuerT;


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

   function TheMechanism (Contents : ContentsT)
         return CryptoTypes.AlgorithmT;


   ------------------------------------------------------------------
   -- IsCurrent
   --
   -- Description:
   --    Determines whether the certificate is current
   --
   -- Traceunit : C.Cert.IsCurrent
   -- Traceto   : FD.Certificate.IsCurrent
   ------------------------------------------------------------------

   function IsCurrent (Contents : ContentsT) return Boolean;
   --# global Clock.CurrentTime;


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
         return CertTypes.RawDataT;

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
                         IsKnown   :    out Boolean );
   --# global in     KeyStore.Store;
   --#        in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out AuditLog.FileState;
   --#        in out AuditLog.State;
   --# derives IsKnown            from Contents,
   --#                                 KeyStore.Store &
   --#         AuditLog.FileState from *,
   --#                                 ConfigData.State,
   --#                                 Contents,
   --#                                 KeyStore.Store,
   --#                                 AuditLog.State,
   --#                                 Clock.Now &
   --#         AuditLog.State     from *,
   --#                                 Contents,
   --#                                 KeyStore.Store,
   --#                                 AuditLog.FileState,
   --#                                 Clock.Now,
   --#                                 ConfigData.State;
   --# post IsKnown <-> KeyStore.Prf_IssuerKeyNotNull(prf_idIssuer(Contents), KeyStore.Store);


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
                   IsVerified :    out Boolean);
   --# global in     KeyStore.Store;
   --#        in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out AuditLog.FileState;
   --#        in out AuditLog.State;
   --# derives AuditLog.FileState,
   --#         AuditLog.State     from Contents,
   --#                                 KeyStore.Store,
   --#                                 AuditLog.FileState,
   --#                                 AuditLog.State,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 RawCert &
   --#         IsVerified         from Contents,
   --#                                 KeyStore.Store,
   --#                                 RawCert;


   private

      type ContentsT is tagged
         record
            ID        : CertTypes.IDT;
            NotBefore : Clock.TimeT;
            NotAfter  : Clock.TimeT;
            Mechanism : CryptoTypes.AlgorithmT;
         end record;

     NullContents : constant ContentsT :=
       ContentsT'( ID        => CertTypes.NullID,
                   NotBefore => Clock.ZeroTime,
                   NotAfter  => Clock.ZeroTime,
                   Mechanism => CryptoTypes.AlgorithmT'First);

--# accept W, 394, ContentsT, "Child packages supply constructors for ContentsT";
end Cert;
