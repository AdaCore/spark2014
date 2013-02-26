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
-- PrivCert
--
-- Implementation Notes:
--     None
--
------------------------------------------------------------------
with CertProcessing,
     Clock;

package body Cert.Attr.Priv is

   ------------------------------------------------------------------
   -- TheRole
   --
   -- Implementation Notes:
   --     None
   ------------------------------------------------------------------

   function TheRole (Contents : ContentsT) return PrivTypes.PrivilegeT
   is
   begin
      return Contents.Role;
   end TheRole;


   ------------------------------------------------------------------
   -- TheClearance
   --
   -- Implementation Notes:
   --     None
   ------------------------------------------------------------------

   function TheClearance (Contents : ContentsT) return PrivTypes.ClearanceT
   is
   begin
      return Contents.Clearance;
   end TheClearance;


   ------------------------------------------------------------------
   -- Extract
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure Extract (RawCert  : in     CertTypes.RawCertificateT;
                      Contents :    out ContentsT;
                      Success  :    out Boolean)
   is
      LocalContents : CertProcessing.PrivCertDataT;
      Extracted,
      NotBeforeOk,
      NotAfterOk    : Boolean;
   begin
      CertProcessing.ExtractPrivCertData(RawPrivCert    => RawCert,
                                         PrivCert       => LocalContents,
                                         ExtractSuccess => Extracted);

      Contents.ID.Issuer       := LocalContents.Issuer;
      Contents.ID.SerialNumber
        := CertTypes.SerialNumberT(LocalContents.SerialNumber);
      Contents.Mechanism       := LocalContents.SigAlgID;
      Contents.BaseCertID      := LocalContents.Holder;
      Contents.Role            := LocalContents.Privilege.Role;
      Contents.Clearance.Class := LocalContents.Privilege.Class;

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
   --     None
   ------------------------------------------------------------------
   procedure Clear (Contents :    out ContentsT)
   is
   begin
      Contents := NullContents;
   end Clear;


end Cert.Attr.Priv;
