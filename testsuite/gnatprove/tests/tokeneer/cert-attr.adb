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
-- AttrCert
--
--  Implementation Notes:
--      None.
--
------------------------------------------------------------------

package body Cert.Attr is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------

   ------------------------------------------------------------------
   -- ExtractUser
   --
   -- Implementation Notes:
   --     Prints the Issuer ID& SerialNumber.
   ------------------------------------------------------------------

   function ExtractUser (Contents : ContentsT) return AuditTypes.UserTextT is
      LocalUser : AuditTypes.UserTextT := AuditTypes.NoUser;
      FullString : String := "Issuer: "
        & CryptoTypes.IssuerIdT'Image (Contents.BaseCertID.Issuer.ID)
        & " SerialNo:  "
        & CertTypes.SerialNumberT'Image (Contents.BaseCertID.SerialNumber);

   begin
      -- the Full string is short enough to use it all
      LocalUser (1 .. FullString'Last) := FullString;

      return LocalUser;
   end ExtractUser;

   ------------------------------------------------------------------
   -- TheBaseCert
   --
   -- Implementation Notes:
   --     None
   ------------------------------------------------------------------

   function TheBaseCert (Contents : ContentsT) return CertTypes.IDT is
     (Contents.BaseCertID);
end Cert.Attr;
