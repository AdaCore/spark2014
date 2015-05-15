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
-- IandACert
--
-- Implementation Notes:
--    None.
--
------------------------------------------------------------------
with Clock,
     CertProcessing;

package body Cert.Attr.IandA is

   ------------------------------------------------------------------
   -- TheTemplate
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   function TheTemplate (Contents : ContentsT) return IandATypes.TemplateT is
     (Contents.Template);

   ------------------------------------------------------------------
   -- Extract
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure Extract (RawCert  : in     CertTypes.RawCertificateT;
                      Contents :    out ContentsT;
                      Success  :    out Boolean)
   is
      LocalContents : CertProcessing.IACertDataT;
      Extracted,
      NotBeforeOk,
      NotAfterOk    : Boolean;
   begin
      CertProcessing.ExtractIACertData(RawIACert      => RawCert,
                                       IACert         => LocalContents,
                                       ExtractSuccess => Extracted);

      Contents.ID.Issuer       := LocalContents.Issuer;
      Contents.ID.SerialNumber
        := CertTypes.SerialNumberT(LocalContents.SerialNumber);
      Contents.Mechanism       := LocalContents.SigAlgID;
      Contents.BaseCertID      := LocalContents.Holder;
      Contents.Template        := LocalContents.Template;

      -- NotBefore and NotAfter are read as 5 unsigned 32 bit words -
      -- convert to Clock.TimeT
      Clock.ConstructTime(
               Year    => LocalContents.AttCertValidity.NotBefore.Year,
               Month   => LocalContents.AttCertValidity.NotBefore.Month,
               Day     => LocalContents.AttCertValidity.NotBefore.Day,
               Hour    => LocalContents.AttCertValidity.NotBefore.Hour,
               Min     => LocalContents.AttCertValidity.NotBefore.Minute,
               TheTime => Contents.NotBefore,
               Success => NotBeforeOK);

      Clock.ConstructTime(
               Year    => LocalContents.AttCertValidity.NotAfter.Year,
               Month   => LocalContents.AttCertValidity.NotAfter.Month,
               Day     => LocalContents.AttCertValidity.NotAfter.Day,
               Hour    => LocalContents.AttCertValidity.NotAfter.Hour,
               Min     => LocalContents.AttCertValidity.NotAfter.Minute,
               TheTime => Contents.NotAfter,
               Success => NotAfterOK);

      Success := Extracted and NotBeforeOK and NotAfterOK;
   end Extract;

   ------------------------------------------------------------------
   -- Clear
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure Clear (Contents :    out ContentsT)
   is
   begin
      Contents := NullContents;
   end Clear;

   --  Converts the extended type to the original one.
   function Cert_Attr_Ianda_To_Cert (Contents : in ContentsT)
                                    return Cert.ContentsT is
     (Cert.ContentsT'(ID        => Contents.ID,
                      NotBefore => Contents.NotBefore,
                      NotAfter  => Contents.NotAfter,
                      Mechanism => Contents.Mechanism));

   --  Converts the extended type to the original one.
   function Cert_Attr_Ianda_To_Cert_Attr (Contents : in ContentsT)
                                         return Cert.Attr.ContentsT is
     (Cert.Attr.ContentsT'(ID         => Contents.ID,
                           NotBefore  => Contents.NotBefore,
                           NotAfter   => Contents.NotAfter,
                           Mechanism  => Contents.Mechanism,
                           BaseCertID => Contents.BaseCertID));
end Cert.Attr.IandA;
