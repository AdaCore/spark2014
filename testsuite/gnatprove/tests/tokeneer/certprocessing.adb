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
-- Implementation Notes:
--    Uses the (non-SPARK) CertProc support package.
--
------------------------------------------------------------------

with CertProc;

package body CertProcessing is
   ------------------------------------------------------------------
   -- Exported Subprograms
   ------------------------------------------------------------------
   ------------------------------------------------------------------
   -- ExtractIDCertData
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure ExtractIDCertData
     (RawIDCert      : in     CertTypes.RawCertificateT;
      IDCert         :    out IDCertDataT;
      ExtractSuccess :    out Boolean)
   is
      LocalData : CertProc.IDCertDataT;
   begin
      CertProc.ExtractIDCertData(RawIDCert      => RawIDCert,
                                 IDCert         => LocalData,
                                 ExtractSuccess => ExtractSuccess);

      IDCert := (SerialNumber => LocalData.SerialNumber,
                 SigAlgId     => LocalData.SigAlgID,
                 Issuer       => LocalData.Issuer,
                 Validity     =>
                    (NotBefore =>
                       (Minute => LocalData.Validity.NotBefore.Minute,
                        Hour   => LocalData.Validity.NotBefore.Hour,
                        Day    => LocalData.Validity.NotBefore.Day,
                        Month  => LocalData.Validity.NotBefore.Month,
                        Year   => LocalData.Validity.NotBefore.Year),
                     NotAfter =>
                       (Minute => LocalData.Validity.NotAfter.Minute,
                        Hour   => LocalData.Validity.NotAfter.Hour,
                        Day    => LocalData.Validity.NotAfter.Day,
                        Month  => LocalData.Validity.NotAfter.Month,
                        Year   => LocalData.Validity.NotAfter.Year)),
                 Subject      => LocalData.Subject,
                 SubjectPublicKeyInfo =>
                    (AlgorithmID => LocalData.SubjectPublicKeyInfo.AlgorithmID,
                     KeyID       => LocalData.SubjectPublicKeyInfo.KeyID,
                     KeyLength   => LocalData.SubjectPublicKeyInfo.KeyLength));
   end ExtractIDCertData;

   ------------------------------------------------------------------
   -- ExtractPrivCertData
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure ExtractPrivCertData
     (RawPrivCert    : in     CertTypes.RawCertificateT;
      PrivCert       :    out PrivCertDataT;
      ExtractSuccess :    out Boolean)
   is
      LocalData : CertProc.PrivCertDataT;
   begin
      CertProc.ExtractPrivCertData(RawPrivCert    => RawPrivCert,
                                   PrivCert       => LocalData,
                                   ExtractSuccess => ExtractSuccess);

      PrivCert := (Holder       => LocalData.Holder,
                   Issuer       => LocalData.Issuer,
                   SigAlgId     => LocalData.SigAlgID,
                   SerialNumber => LocalData.SerialNumber,
                   AttCertValidity =>
                      (NotBefore =>
                         (Minute => LocalData.AttCertValidity.NotBefore.Minute,
                          Hour   => LocalData.AttCertValidity.NotBefore.Hour,
                          Day    => LocalData.AttCertValidity.NotBefore.Day,
                          Month  => LocalData.AttCertValidity.NotBefore.Month,
                          Year   => LocalData.AttCertValidity.NotBefore.Year),
                       NotAfter =>
                         (Minute => LocalData.AttCertValidity.NotAfter.Minute,
                          Hour   => LocalData.AttCertValidity.NotAfter.Hour,
                          Day    => LocalData.AttCertValidity.NotAfter.Day,
                          Month  => LocalData.AttCertValidity.NotAfter.Month,
                          Year   => LocalData.AttCertValidity.NotAfter.Year)),
                   Privilege    =>
                      (Role  => LocalData.Privilege.Role,
                       Class => LocalData.Privilege.Class));
   end ExtractPrivCertData;

   ------------------------------------------------------------------
   -- ExtractIACertData
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure ExtractIACertData
     (RawIACert      : in     CertTypes.RawCertificateT;
      IACert         :    out IACertDataT;
      ExtractSuccess :    out Boolean)
   is
      LocalData : CertProc.IACertDataT;
   begin
      CertProc.ExtractIACertData(RawIACert      => RawIACert,
                                 IACert         => LocalData,
                                 ExtractSuccess => ExtractSuccess);

      IACert := (Holder          => LocalData.Holder,
                 Issuer          => LocalData.Issuer,
                 SigAlgId        => LocalData.SigAlgID,
                 SerialNumber    => LocalData.SerialNumber,
                 AttCertValidity =>
                    (NotBefore =>
                       (Minute => LocalData.AttCertValidity.NotBefore.Minute,
                        Hour   => LocalData.AttCertValidity.NotBefore.Hour,
                        Day    => LocalData.AttCertValidity.NotBefore.Day,
                        Month  => LocalData.AttCertValidity.NotBefore.Month,
                        Year   => LocalData.AttCertValidity.NotBefore.Year),
                     NotAfter  =>
                       (Minute => LocalData.AttCertValidity.NotAfter.Minute,
                        Hour   => LocalData.AttCertValidity.NotAfter.Hour,
                        Day    => LocalData.AttCertValidity.NotAfter.Day,
                        Month  => LocalData.AttCertValidity.NotAfter.Month,
                        Year   => LocalData.AttCertValidity.NotAfter.Year)),
                 Template        => LocalData.Template);
   end ExtractIACertData;

   ------------------------------------------------------------------
   -- ExtractAuthCertData
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure ExtractAuthCertData
     (RawAuthCert    : in     CertTypes.RawCertificateT;
      AuthCert       :    out AuthCertDataT;
      ExtractSuccess :    out Boolean)
   is
      LocalData : CertProc.AuthCertDataT;
   begin
      CertProc.ExtractAuthCertData(RawAuthCert => RawAuthCert,
                                   AuthCert    => LocalData,
                                   ExtractSuccess => ExtractSuccess);

      AuthCert := (Holder       => LocalData.Holder,
                   Issuer       => LocalData.Issuer,
                   SigAlgId     => LocalData.SigAlgID,
                   SerialNumber => LocalData.SerialNumber,
                   AttCertValidity =>
                      (NotBefore =>
                         (Minute => LocalData.AttCertValidity.NotBefore.Minute,
                          Hour   => LocalData.AttCertValidity.NotBefore.Hour,
                          Day    => LocalData.AttCertValidity.NotBefore.Day,
                          Month  => LocalData.AttCertValidity.NotBefore.Month,
                          Year   => LocalData.AttCertValidity.NotBefore.Year),
                       NotAfter =>
                         (Minute => LocalData.AttCertValidity.NotAfter.Minute,
                          Hour   => LocalData.AttCertValidity.NotAfter.Hour,
                          Day    => LocalData.AttCertValidity.NotAfter.Day,
                          Month  => LocalData.AttCertValidity.NotAfter.Month,
                          Year   => LocalData.AttCertValidity.NotAfter.Year)),
                   Privilege    =>
                      (Role  => LocalData.Privilege.Role,
                       Class => LocalData.Privilege.Class));
   end ExtractAuthCertData;

   ------------------------------------------------------------------
   -- ObtainRawData
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure ObtainRawData
     (RawCert       : in     CertTypes.RawCertificateT;
      RawData       :    out CertTypes.RawDataT;
      ObtainSuccess :    out Boolean)
   is
   begin
      CertProc.ObtainRawData(RawCert       => RawCert,
                             RawData       => RawData,
                             ObtainSuccess => ObtainSuccess);
   end ObtainRawData;

   ------------------------------------------------------------------
   -- ObtainSignatureData
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure ObtainSignatureData
     (RawCert       : in     CertTypes.RawCertificateT;
      SignatureData :    out CertTypes.SignatureT;
      ObtainSuccess :    out Boolean)
   is
   begin
      CertProc.ObtainSignatureData(RawCert       => RawCert,
                                   SignatureData => SignatureData,
                                   ObtainSuccess => ObtainSuccess);
   end ObtainSignatureData;

   ------------------------------------------------------------------
   -- ConstructAuthCert
   --
   -- Implementation Notes:
   --    Adds the fictional Crypto dictionary (copied from the Priv Cert)
   --
   ------------------------------------------------------------------
   procedure ConstructAuthCert
     (AuthCert            : in     AuthCertDataT;
      UnsignedRawAuthCert :    out CertTypes.RawCertificateT)
   is
      LocalCert : CertProc.AuthCertDataT :=
                  (CertType        => CertProc.AuthCertType,
                   Holder          => AuthCert.Holder,
                   Issuer          => AuthCert.Issuer,
                   SigAlgId        => AuthCert.SigAlgID,
                   SerialNumber    => AuthCert.SerialNumber,
                   AttCertValidity =>
                      (NotBefore =>
                         (Minute => AuthCert.AttCertValidity.NotBefore.Minute,
                          Hour   => AuthCert.AttCertValidity.NotBefore.Hour,
                          Day    => AuthCert.AttCertValidity.NotBefore.Day,
                          Month  => AuthCert.AttCertValidity.NotBefore.Month,
                          Year   => AuthCert.AttCertValidity.NotBefore.Year),
                       NotAfter  =>
                         (Minute => AuthCert.AttCertValidity.NotAfter.Minute,
                          Hour   => AuthCert.AttCertValidity.NotAfter.Hour,
                          Day    => AuthCert.AttCertValidity.NotAfter.Day,
                          Month  => AuthCert.AttCertValidity.NotAfter.Month,
                          Year   => AuthCert.AttCertValidity.NotAfter.Year)),
                   Privilege       =>
                      (Role  => AuthCert.Privilege.Role,
                       Class => AuthCert.Privilege.Class));

   begin
      CertProc.ConstructAuthCert(AuthCert            => LocalCert,
                                 UnsignedRawAuthCert => UnsignedRawAuthCert);
   end ConstructAuthCert;

   ------------------------------------------------------------------
   -- AddAuthSignature
   --
   -- Implementation Notes:
   --    Adds the 'SignatureData' key and encloses the data with braces.
   --    Digest ID in SignatureData is the 'correct' ID - i.e.the ID created
   --    from digesting the unsigned cert.This needs to overwrite the
   --    DigestID in the fictional Crypto dictionary.
   --
   ------------------------------------------------------------------
   procedure AddAuthSignature
     (UnsignedRawAuthCert : in     CertTypes.RawCertificateT;
      SignatureData       : in     CertTypes.SignatureT;
      SignedRawAuthCert   :    out CertTypes.RawCertificateT)
   is
   begin
      CertProc.AddAuthSignature(UnsignedRawAuthCert => UnsignedRawAuthCert,
                                SignatureData       => SignatureData,
                                SignedRawAuthCert   => SignedRawAuthCert);
   end AddAuthSignature;

end CertProcessing;
