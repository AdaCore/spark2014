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
-- CertTypes
--
-- Description:
--    Types that appear within the context of a certificate
--
------------------------------------------------------------------
with CommonTypes,
     CryptoTypes;

package CertTypes is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------

   -- A raw certificate read from the card reader is simply a string.
   -- Max length set by SPRE.
   MaxRawCertLength : constant Positive := 4096;
   subtype RawCertificateI is Positive range 1..MaxRawCertLength;
   subtype RawCertificateT is String(RawCertificateI);

   NullRawCertificate : constant RawCertificateT :=
     RawCertificateT'(others => ' ');

   -- This certificate can then be split into the data part and the
   -- signature part.
   --
   -- RAWDATA has the same string size as a (signed) raw certificate,
   -- but includes a length field.
   type RawDataT is record
      RawData    : RawCertificateT;
      DataLength : RawCertificateI;
   end record;

   -- The different types of certificates handled by TIS
   type CertificateT is (IDCert, AuthCert, PrivCert, IandACert);


   -- SIGDATA
   MaxSigDataLength : constant Positive := 4096;
   subtype SigDataI is Positive range 1..MaxSigDataLength;
   subtype SigDataT is String(SigDataI);
   type SignatureT  is record
      SigData   : SigDataT;
      SigLength : SigDataI;
   end record;

   type SerialNumberT is range 0..2**32 - 1;

   function SerialNumberT_Image (X : SerialNumberT) return CommonTypes.StringF1L2to1000 is
      (SerialNumberT'Image (X));
   pragma Annotate (GNATprove, False_Positive,
                    "predicate check might fail",
                    "Image of integers of type SerialNumberT are short strings starting at index 1");

   -- Certificate ID
   type IDT is record
      Issuer       : CryptoTypes.IssuerT;
      SerialNumber : SerialNumberT;
   end record;

   NullID : constant IDT := IDT'(Issuer       => CryptoTypes.NullIssuer,
                                 SerialNumber => SerialNumberT'First);

end CertTypes;
