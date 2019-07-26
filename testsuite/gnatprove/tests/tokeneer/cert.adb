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
-- Cert
--
-- Description:
--   Implements common components of all certificates.
--
------------------------------------------------------------------

with CommonTypes,
     CertProcessing,
     KeyStore;

package body Cert is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------


   ------------------------------------------------------------------
   -- Public Operations
   --
   ------------------------------------------------------------------
   ------------------------------------------------------------------
   -- TheIssuer
   --
   -- Implementation Notes:
   --     None.
   ------------------------------------------------------------------
   function TheIssuer (Contents : ContentsT) return CryptoTypes.IssuerT is
     (Contents.ID.Issuer);

   ------------------------------------------------------------------
   -- TheID
   --
   -- Implementation Notes:
   --     None.
   ------------------------------------------------------------------
   function TheID (Contents : ContentsT) return CertTypes.IDT is (Contents.ID);

   ------------------------------------------------------------------
   -- ExtractUser
   --
   -- Implementation Notes:
   --     Prints the Issuer ID& SerialNumber.
   ------------------------------------------------------------------
   function ExtractUser (Contents : ContentsT) return AuditTypes.UserTextT is
      LocalUser : AuditTypes.UserTextT := AuditTypes.NoUser;
      FullString : String := "Issuer: "
        & CryptoTypes.IssuerIdT'Image (Contents.ID.Issuer.ID)
        & " SerialNo:  "
        & CertTypes.SerialNumberT'Image (Contents.ID.SerialNumber);
   begin
      -- the Full string is short enough to use it all
      LocalUser (1 .. FullString'Last) := FullString;

      return LocalUser;
   end ExtractUser;

   ------------------------------------------------------------------
   -- TheMechanism
   --
   -- Implementation Notes:
   --     None.
   ------------------------------------------------------------------
   function TheMechanism (Contents : ContentsT) return CryptoTypes.AlgorithmT
   is
     (Contents.Mechanism);

   ------------------------------------------------------------------
   -- IsCurrent
   --
   -- Implementation Notes:
   --     None.
   ------------------------------------------------------------------
   function IsCurrent (Contents : ContentsT) return Boolean is
     (Clock.GreaterThanOrEqual(Clock.TheCurrentTime, Contents.NotBefore) and
      Clock.LessThanOrEqual(Clock.TheCurrentTime, Contents.NotAfter));

   ------------------------------------------------------------------
   -- GetData
   --
   -- Implementation Notes:
   --    Deletes the Signature data from RawCert
   ------------------------------------------------------------------
   function GetData (RawCert : CertTypes.RawCertificateT)
                    return CertTypes.RawDataT
   is
      LocalRawData : CertTypes.RawDataT;
      Ignored      : Boolean;
   begin
      pragma Warnings (Off);
      CertProcessing.ObtainRawData(RawCert       => RawCert,
                                   RawData       => LocalRawData,
                                   ObtainSuccess => Ignored);
      pragma Warnings (On);
      return LocalRawData;
   end GetData;

   ------------------------------------------------------------------
   -- GetSignature
   --
   -- Implementation Notes:
   --     None.
   ------------------------------------------------------------------
   function GetSignature (RawCert : CertTypes.RawCertificateT)
                         return CertTypes.SignatureT
   is
      LocalSig : CertTypes.SignatureT;
      Ignored  : Boolean;
   begin
      pragma Warnings (Off);
      CertProcessing.ObtainSignatureData(RawCert       => RawCert,
                                         SignatureData => LocalSig,
                                         ObtainSuccess => Ignored);
      pragma Warnings (On);
      return LocalSig;
   end GetSignature;

   ------------------------------------------------------------------
   -- IssuerKnown
   --
   -- Implementation Notes:
   --     None
   ------------------------------------------------------------------
   procedure IssuerKnown (Contents : in     ContentsT;
                          IsKnown  :    out Boolean)
   is
   begin
      KeyStore.KeyMatchingIssuerPresent
        (Issuer    => Contents.ID.Issuer,
         IsPresent => IsKnown);
   end IssuerKnown;

   ------------------------------------------------------------------
   -- IsOK
   --
   -- Implementation Notes:
   --     None.
   ------------------------------------------------------------------
   procedure IsOK (RawCert    : in     CertTypes.RawCertificateT;
                   Contents   : in     ContentsT;
                   IsVerified :    out Boolean)
   is
      IsKnown : Boolean;
   begin

       IssuerKnown(Contents => Contents,
                   IsKnown  => IsKnown);

       if IsKnown then
          KeyStore.IsVerifiedBy
            (Mechanism   => Contents.Mechanism,
             RawCertData => GetData(RawCert),
             Signature   => GetSignature(RawCert),
             TheIssuer   => Contents.ID.Issuer,
             Verified    => IsVerified);

       else
          IsVerified := False;
       end if;
   end IsOK;

end Cert;
