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
-- CertProcessing
--
-- Description:
--    A thin SPARK layer for the certificate processing library
--
------------------------------------------------------------------

with CommonTypes,
     CertTypes,
     CryptoTypes,
     IandATypes,
     PrivTypes;


package CertProcessing is

   ------------------------------------------------------------------
   --
   -- Types
   --
   ------------------------------------------------------------------

   -- ValidityT is a set of two times - NotBefore and NotAfter.These times
   -- are returned from the certificate processing library as five 32-bit
   -- words.
   type TimeT is record
      Year,
      Month,
      Day,
      Hour,
      Minute : CommonTypes.Unsigned32T;
   end record;

   type ValidityT is record
      NotBefore : TimeT;
      NotAfter  : TimeT;
   end record;

   -- PrivilegeT holds the role and class of the certificate owner
   type PrivilegeT is record
      Role  : PrivTypes.PrivilegeT;
      Class : PrivTypes.ClassT;
   end record;

   -- PublicKeyInfoT holds the public key of the certificate owner
   type PublicKeyInfoT is record
      AlgorithmId : CryptoTypes.AlgorithmT;
      KeyID       : CommonTypes.Unsigned32T;
      KeyLength   : CommonTypes.Unsigned32T;
   end record;

   -- The XXCertDataT types represent the actual data stored in each
   -- certificate type.
   type IDCertDataT is record
      SerialNumber         : CommonTypes.Unsigned32T;
      SigAlgId             : CryptoTypes.AlgorithmT;
      Issuer               : CryptoTypes.IssuerT;
      Validity             : ValidityT;
      Subject              : CryptoTypes.IssuerT;
      SubjectPublicKeyInfo : PublicKeyInfoT;
   end record;

   type PrivCertDataT is record
      Holder          : CertTypes.IDT;
      Issuer          : CryptoTypes.IssuerT;
      SigAlgId        : CryptoTypes.AlgorithmT;
      SerialNumber    : CommonTypes.Unsigned32T;
      AttCertValidity : ValidityT;
      Privilege       : PrivilegeT;
   end record;

   type AuthCertDataT is record
      Holder          : CertTypes.IDT;
      Issuer          : CryptoTypes.IssuerT;
      SigAlgId        : CryptoTypes.AlgorithmT;
      SerialNumber    : CommonTypes.Unsigned32T;
      AttCertValidity : ValidityT;
      Privilege       : PrivilegeT;
   end record;

   type IACertDataT is record
      Holder          : CertTypes.IDT;
      Issuer          : CryptoTypes.IssuerT;
      SigAlgId        : CryptoTypes.AlgorithmT;
      SerialNumber    : CommonTypes.Unsigned32T;
      AttCertValidity : ValidityT;
      Template        : IandATypes.TemplateT;
   end record;


   ------------------------------------------------------------------
   -- ExtractIDCertData
   --
   -- Description:
   --    Takes the raw certificate data extracted from the user's token, and
   --    converts into the correct (ID) certificate structure.
   --
   -- Traceunit : C.CertProcessing.ExtractIDCertData
   -- Traceto   : FD.Types.Certificates
   ------------------------------------------------------------------
   procedure ExtractIDCertData
     (RawIDCert      : in     CertTypes.RawCertificateT;
      IDCert         :    out IDCertDataT;
      ExtractSuccess :    out Boolean)
     with Global  => null,
          Depends => ((ExtractSuccess,
                       IDCert)         => RawIDCert);

   ------------------------------------------------------------------
   -- ExtractPrivCertData
   --
   -- Description:
   --    Takes the raw certificate data extracted from the user's token, and
   --    converts into the correct (Priv) certificate structure.
   --
   -- Traceunit : C.CertProcessing.ExtractPrivCertData
   -- Traceto   : FD.Types.Certificates
   ------------------------------------------------------------------
   procedure ExtractPrivCertData
     (RawPrivCert    : in     CertTypes.RawCertificateT;
      PrivCert       :    out PrivCertDataT;
      ExtractSuccess :    out Boolean)
     with Global  => null,
          Depends => ((ExtractSuccess,
                       PrivCert)       => RawPrivCert);

   ------------------------------------------------------------------
   -- ExtractIACertData
   --
   -- Description:
   --    Takes the raw certificate data extracted from the user's token, and
   --    converts into the correct (I&A) certificate structure.
   --
   -- Traceunit : C.CertProcessing.ExtractIACertData
   -- Traceto   : FD.Types.Certificates
   ------------------------------------------------------------------
   procedure ExtractIACertData
     (RawIACert      : in     CertTypes.RawCertificateT;
      IACert         :    out IACertDataT;
      ExtractSuccess :    out Boolean)
     with Global  => null,
          Depends => ((ExtractSuccess,
                       IACert)         => RawIACert);

   ------------------------------------------------------------------
   -- ExtractAuthCertData
   --
   -- Description:
   --    Takes the raw certificate data extracted from the user's token, and
   --    converts into the correct (Auth) certificate structure.
   --
   -- Traceunit : C.CertProcessing.ExtractAuthCertData
   -- Traceto   : FD.Types.Certificates
   ------------------------------------------------------------------
   procedure ExtractAuthCertData
     (RawAuthCert    : in     CertTypes.RawCertificateT;
      AuthCert       :    out AuthCertDataT;
      ExtractSuccess :    out Boolean)
     with Global  => null,
          Depends => ((AuthCert,
                       ExtractSuccess) => RawAuthCert);

   ------------------------------------------------------------------
   -- ObtainRawData
   --
   -- Description:
   --    Extracts the raw data from the raw certificate.
   --
   -- Traceunit : C.CertProcessing.ObtainRawData
   -- Traceto   : FD.Types.Certificates
   ------------------------------------------------------------------
   procedure ObtainRawData(
                   RawCert       : in     CertTypes.RawCertificateT;
                   RawData       :    out CertTypes.RawDataT;
                   ObtainSuccess :    out Boolean
                   )
     with Global  => null,
          Depends => ((ObtainSuccess,
                       RawData)       => RawCert);

   ------------------------------------------------------------------
   -- ObtainSignatureData
   --
   -- Description:
   --    Extracts the signature data from the raw certificate.
   --
   -- Traceunit : C.CertProcessing.ObtainSignatureData
   -- Traceto   : FD.Types.Certificates
   ------------------------------------------------------------------
   procedure ObtainSignatureData(
                   RawCert       : in     CertTypes.RawCertificateT;
                   SignatureData :    out CertTypes.SignatureT;
                   ObtainSuccess :    out Boolean
                   )
     with Global  => null,
          Depends => ((ObtainSuccess,
                       SignatureData) => RawCert);

   ------------------------------------------------------------------
   -- ConstructAuthCert
   --
   -- Description:
   --    Constructs the raw data of an authorization certificate
   --    (prior to being signed).
   --
   -- Traceunit : C.CertProcessing.ConstructAuthCert
   -- Traceto   : FD.Types.Certificates
   --             FD.Certificate.NewAuthCert
   ------------------------------------------------------------------
   procedure ConstructAuthCert
     (AuthCert            : in     AuthCertDataT;
      UnsignedRawAuthCert :    out CertTypes.RawCertificateT)
     with Global  => null,
          Depends => (UnsignedRawAuthCert => AuthCert);

   ------------------------------------------------------------------
   -- AddAuthSignature
   --
   -- Description:
   --    Appends the supplied signature to the certificate data, ready for
   --    writing to the user's card.
   --
   -- Traceunit : C.CertProcessing.AddAuthSignature
   -- Traceto   : FD.Certificate.NewAuthCert
   ------------------------------------------------------------------
   procedure AddAuthSignature
     (UnsignedRawAuthCert : in     CertTypes.RawCertificateT;
      SignatureData       : in     CertTypes.SignatureT;
      SignedRawAuthCert   :    out CertTypes.RawCertificateT)
     with Global  => null,
          Depends => (SignedRawAuthCert => (SignatureData,
                                            UnsignedRawAuthCert));

end CertProcessing;
