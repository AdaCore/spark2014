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
--# inherit BasicTypes,
--#         Cert,
--#         CertProcessing,
--#         CertTypes,
--#         Clock,
--#         CryptoTypes;

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
   type ContentsT is new Cert.ContentsT with private;


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
                      Success  :    out Boolean);
   --# derives Contents,
   --#         Success from RawCert;


   ------------------------------------------------------------------
   -- Clear
   --
   -- Description:
   --    Clears the contents of the certificate
   --
   -- Traceunit : C.IDCert.Clear
   --
   ------------------------------------------------------------------
   procedure Clear (Contents :    out ContentsT);
   --# derives Contents from ;


   private
      type ContentsT is new Cert.ContentsT with
         record
            Subject          : CryptoTypes.IssuerT;
            SubjectPublicKey : CryptoTypes.KeyPartT;
         end record;

     NullContents : constant ContentsT :=
       ContentsT'( Cert.NullContents with
                   Subject   => CryptoTypes.NullIssuer,
                   SubjectPublicKey => CryptoTypes.NullKeyPart);


end Cert.ID;
