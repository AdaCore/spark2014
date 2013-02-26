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
-- IandACert
--
-- Description:
--    Defines the contents of an I&A certificate, and provides
--    operations on those contents.
--    Certificates enter the system as raw data, and are stored in
--    an internally-defined record structure.
--    Inherits the operations defined in AttrCert.
--
------------------------------------------------------------------

with Cert.Attr,
     CertTypes,
     IandATypes;
--# inherit Cert.Attr,
--#         CertProcessing,
--#         CertTypes,
--#         Clock,
--#         IandATypes;

package Cert.Attr.IandA is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   ------------------------------------------------------------------
   -- ContentsT
   --
   -- Description:
   --    Contents of an I&A certificate
   --
   -- Traceunit : C.IandACert.Contents
   -- Traceto   : FD.Types.Certificates
   ------------------------------------------------------------------
   type ContentsT is new Attr.ContentsT with private;


   ------------------------------------------------------------------
   -- TheTemplate
   --
   -- Description:
   --    Retrieves the biometric template from an I&A certificate.
   --
   -- Traceunit : C.IandACert.TheTemplate
   -- Traceto   : FD.Types.Certificates
   ------------------------------------------------------------------

   function TheTemplate (Contents : ContentsT) return IandATypes.TemplateT;


   ------------------------------------------------------------------
   -- Extract
   --
   -- Description:
   --    Extracts the contents of the raw certificate.
   --
   -- Traceunit : C.IandACert.Extract
   -- Traceto   : FD.Types.Certificates
   ------------------------------------------------------------------
   procedure Extract (RawCert  : in     CertTypes.RawCertificateT;
                      Contents :    out ContentsT;
                      Success  :    out Boolean);
   --# derives Contents,
   --#         Success  from RawCert;


   ------------------------------------------------------------------
   -- Clear
   --
   -- Description:
   --    Clears the contents of the certificate
   --
   -- Traceunit : C.IandACert.Clear
   --
   ------------------------------------------------------------------
   procedure Clear (Contents :    out ContentsT);
   --# derives Contents from ;


   private
      type ContentsT is new Attr.ContentsT with
         record
            Template : IandATypes.TemplateT;
         end record;

     NullContents : constant ContentsT :=
       ContentsT'( Attr.NullContents with
                   Template  => IandATypes.NullTemplate);


end Cert.Attr.IandA;
