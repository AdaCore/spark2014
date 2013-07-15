------------------------------------------------------------------
-- Tokeneer ID Station Support Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency. All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd. under contract to the National Security Agency.
------------------------------------------------------------------

------------------------------------------------------------------
-- CertProc
--
-- Description:
--    This stub essentially performs two functions - to extract data
--    from 'raw' certificates, and to construct 'raw' authorization
--    certificates.
--
------------------------------------------------------------------

with BasicTypes;
with IandATypes;
with CertTypes;
with PrivTypes;
with CryptoTypes;

package CertProc is

   ------------------------------------------------------------------
   --
   -- Types
   --
   ------------------------------------------------------------------

   type TimeT is record
      Year,
      Month,
      Day,
      Hour,
      Minute : BasicTypes.Unsigned32T;
   end record;


   type ValidityT is record
      NotBefore : TimeT;
      NotAfter  : TimeT;
   end record;



   type PrivilegeT is record
      Role  : PrivTypes.PrivilegeT;
      Class : PrivTypes.ClassT;
   end record;

   type PublicKeyInfoT is record
      AlgorithmId : CryptoTypes.AlgorithmT;
      KeyID       : BasicTypes.Unsigned32T;
      KeyLength   : BasicTypes.Unsigned32T;
   end record;

   -- A fictional field called CryptoControlData is held in a raw
   -- certificate. this contains information used to control the
   -- crypto operations.
   -- This type is sufficiently large to hold any valid control data
   subtype CryptoControlDataT is String(1..500);

   NullCryptoControl : constant CryptoControlDataT := (others => ' ');

   -- The XXCertDataT types represent the actual data stored in the
   -- certificate and as such, don't include the signature data or
   -- the fictional CryptoControl data. Certificate structures are
   -- defined in section 2.

   type IDCertDataT is record
      CertType             : BasicTypes.Unsigned32T;
      SerialNumber         : BasicTypes.Unsigned32T;
      SigAlgId             : CryptoTypes.AlgorithmT;
      Issuer               : CryptoTypes.IssuerT;
      Validity             : ValidityT;
      Subject              : CryptoTypes.IssuerT;
      SubjectPublicKeyInfo : PublicKeyInfoT;
   end record;


   type PrivCertDataT is record
      CertType        : BasicTypes.Unsigned32T;
      Holder          : CertTypes.IDT;
      Issuer          : CryptoTypes.IssuerT;
      SigAlgId        : CryptoTypes.AlgorithmT;
      SerialNumber    : BasicTypes.Unsigned32T;
      AttCertValidity : ValidityT;
      Privilege       : PrivilegeT;
   end record;

   type AuthCertDataT is record
      CertType        : BasicTypes.Unsigned32T;
      Holder          : CertTypes.IDT;
      Issuer          : CryptoTypes.IssuerT;
      SigAlgId        : CryptoTypes.AlgorithmT;
      SerialNumber    : BasicTypes.Unsigned32T;
      AttCertValidity : ValidityT;
      Privilege       : PrivilegeT;
   end record;

   type IACertDataT is record
      CertType        : BasicTypes.Unsigned32T;
      Holder          : CertTypes.IDT;
      Issuer          : CryptoTypes.IssuerT;
      SigAlgId        : CryptoTypes.AlgorithmT;
      SerialNumber    : BasicTypes.Unsigned32T;
      AttCertValidity : ValidityT;
      Template        : IandATypes.TemplateT;
   end record;


   -- Constants
   IDCertType   : constant BasicTypes.Unsigned32T := 0;
   IACertType   : constant BasicTypes.Unsigned32T := 1;
   PrivCertType : constant BasicTypes.Unsigned32T := 2;
   AuthCertType : constant BasicTypes.Unsigned32T := 3;

   ------------------------------------------------------------------
   -- ExtractIDCertData
   --
   -- Description:
   --    Takes the raw certificate data extracted from the user's token, and
   --    converts into the correct (ID) certificate structure.
   --
   ------------------------------------------------------------------

   procedure ExtractIDCertData(
                   RawIDCert      : in     CertTypes.RawCertificateT;
                   IDCert         :    out IDCertDataT;
                   ExtractSuccess :    out Boolean
                   );


   ------------------------------------------------------------------
   -- ExtractPrivCertData
   --
   -- Description:
   --    Takes the raw certificate data extracted from the user's token, and
   --    converts into the correct (Priv) certificate structure.
   --
   ------------------------------------------------------------------

   procedure ExtractPrivCertData(
                   RawPrivCert    : in     CertTypes.RawCertificateT;
                   PrivCert       :    out PrivCertDataT;
                   ExtractSuccess :    out Boolean
                   );


   ------------------------------------------------------------------
   -- ExtractIACertData
   --
   -- Description:
   --    Takes the raw certificate data extracted from the user's token, and
   --    converts into the correct (I&A) certificate structure.
   --
   ------------------------------------------------------------------

   procedure ExtractIACertData(
                   RawIACert      : in     CertTypes.RawCertificateT;
                   IACert         :    out IACertDataT;
                   ExtractSuccess :    out Boolean
                   );


   ------------------------------------------------------------------
   -- ExtractAuthCertData
   --
   -- Description:
   --    Takes the raw certificate data extracted from the user's token, and
   --    converts into the correct (Auth) certificate structure.
   --
   ------------------------------------------------------------------

   procedure ExtractAuthCertData(
                   RawAuthCert    : in     CertTypes.RawCertificateT;
                   AuthCert       :    out AuthCertDataT;
                   ExtractSuccess :    out Boolean
                   );


   ------------------------------------------------------------------
   -- ObtainRawData
   --
   -- Description:
   --    Extracts the raw certificate data from the raw certificate.
   --    i.e. everything except the signature.
   --
   ------------------------------------------------------------------

   procedure ObtainRawData(
                   RawCert       : in     CertTypes.RawCertificateT;
                   RawData       :    out CertTypes.RawDataT;
                   ObtainSuccess :    out Boolean
                   );

   ------------------------------------------------------------------
   -- ObtainSignatureData
   --
   -- Description:
   --    Extracts the signature data from the raw certificate.
   --    No range checks are performed here. The signature itself
   --    may be longer than expected.
   --
   ------------------------------------------------------------------

   procedure ObtainSignatureData(
                   RawCert       : in     CertTypes.RawCertificateT;
                   SignatureData :    out CertTypes.SignatureT;
                   ObtainSuccess :    out Boolean
                   );


   ------------------------------------------------------------------
   -- ConstructAuthCert
   --
   -- Description:
   --    Constructs a raw authorization certificate (prior to being signed).
   --
   ------------------------------------------------------------------

   procedure ConstructAuthCert(
                   AuthCert            : in     AuthCertDataT;
                   UnsignedRawAuthCert :    out CertTypes.RawCertificateT
                   );


   ------------------------------------------------------------------
   -- AddAuthSignature
   --
   -- Description:
   --    Appends the supplied signature it to the certificate data, ready for
   --    writing to the user's card.
   --
   ------------------------------------------------------------------

   procedure AddAuthSignature(
                   UnsignedRawAuthCert : in     CertTypes.RawCertificateT;
                   SignatureData       : in     CertTypes.SignatureT;
                   SignedRawAuthCert   :    out CertTypes.RawCertificateT);


end CertProc;
