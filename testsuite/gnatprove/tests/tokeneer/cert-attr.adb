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

   function ExtractUser (Contents : ContentsT) return AuditTypes.UserTextT

   is
      LocalUser : AuditTypes.UserTextT := AuditTypes.NoUser;
      FullString : String := "Issuer: "
        & CryptoTypes.IssuerIdT_Image (Contents.BaseCertID.Issuer.ID)
        & " SerialNo:  "
        & CertTypes.SerialNumberT_Image (Contents.BaseCertID.SerialNumber);

   begin
      -- if the Full string is shorter then use it all otherwise
      -- truncate it.

      if FullString'Last <= AuditTypes.UserTextI'Last then
         LocalUser (1 .. FullString'Last) := FullString;
      else
         LocalUser := FullString (1 .. AuditTypes.UserTextI'Last);
      end if;

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
