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
-- Description:
--    Defines the contents of an ID certificate, and provides
--    operations on those contents.
--    Certificates enter the system as raw data, and are stored in
--    an internally-defined record structure.
--    Inherits the operations defined in Cert.
--
------------------------------------------------------------------

with Cert,
     CertTypes,
     CryptoTypes;

package Cert.ID is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   ------------------------------------------------------------------
   -- ContentsT
   --
   -- Description:
   --    Contents of an ID certificate
   --
   -- Traceunit : C.IDCert.Contents
   -- Traceto   : FD.Types.Certificates
   ------------------------------------------------------------------
   type ContentsT is private;


   ------------------------------------------------------------------
   -- TheSubject
   --
   -- Description:
   --    Returns the certificate's subject
   --
   -- Traceunit : C.IDCert.TheSubject
   -- Traceto   : FD.Types.Certificates
   ------------------------------------------------------------------
   function TheSubject (Contents : ContentsT) return CryptoTypes.IssuerT;

   ------------------------------------------------------------------
   -- ThePublicKey
   --
   -- Description:
   --    Returns the subject's public key
   --
   -- Traceunit : C.IDCert.ThePublicKey
   -- Traceto   : FD.Types.Certificates
   ------------------------------------------------------------------
   function ThePublicKey (Contents : ContentsT) return CryptoTypes.KeyPartT;

   ------------------------------------------------------------------
   -- Extract
   --
   -- Description:
   --    Extracts the contents of a raw certificate
   --
   -- Traceunit : C.IDCert.Extract
   -- Traceto   : FD.Types.Certificates
   ------------------------------------------------------------------
   procedure Extract (RawCert  : in     CertTypes.RawCertificateT;
                      Contents :    out ContentsT;
                      Success  :    out Boolean)
     with Global  => null,
          Depends => ((Contents,
                       Success)  => RawCert);

   ------------------------------------------------------------------
   -- Clear
   --
   -- Description:
   --    Clears the contents of the certificate
   --
   -- Traceunit : C.IDCert.Clear
   --
   ------------------------------------------------------------------
   procedure Clear (Contents :    out ContentsT)
     with Global  => null,
          Depends => (Contents => null);

   --  Converts the extended type to the original one.
   function Cert_Id_To_Cert (Contents : in ContentsT) return Cert.ContentsT;

private
   type ContentsT is record
      ID               : CertTypes.IDT;
      NotBefore        : Clock.TimeT;
      NotAfter         : Clock.TimeT;
      Mechanism        : CryptoTypes.AlgorithmT;
      Subject          : CryptoTypes.IssuerT;
      SubjectPublicKey : CryptoTypes.KeyPartT;
   end record;

   NullContents : constant ContentsT :=
     ContentsT'(ID               => CertTypes.NullID,
                NotBefore        => Clock.ZeroTime,
                NotAfter         => Clock.ZeroTime,
                Mechanism        => CryptoTypes.AlgorithmT'First,
                Subject          => CryptoTypes.NullIssuer,
                SubjectPublicKey => CryptoTypes.NullKeyPart);

end Cert.ID;
