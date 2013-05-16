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
-- Cert
--
-- Description:
--   Implements common components of all certificates.
--
------------------------------------------------------------------

with BasicTypes,
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

   function TheIssuer (Contents : ContentsT) return CryptoTypes.IssuerT
   is
   begin
      return Contents.ID.Issuer;
   end TheIssuer;

   ------------------------------------------------------------------
   -- TheID
   --
   -- Implementation Notes:
   --     None.
   ------------------------------------------------------------------

   function TheID (Contents : ContentsT) return CertTypes.IDT
   is
   begin
      return Contents.ID;
   end TheID;


   ------------------------------------------------------------------
   -- ExtractUser
   --
   -- Implementation Notes:
   --     Prints the Issuer ID & SerialNumber.
   ------------------------------------------------------------------

   function ExtractUser (Contents : ContentsT) return AuditTypes.UserTextT
   is
      --# hide ExtractUser;
      LocalUser : AuditTypes.UserTextT := AuditTypes.NoUser;

         FullString : String := "Issuer: "
           & CryptoTypes.IssuerIdT'Image(Contents.ID.Issuer.ID)
           & " SerialNo:  "
           & CertTypes.SerialNumberT'Image(Contents.ID.SerialNumber);
      begin

         -- if the Full string is shorter then use it all otherwise
         -- truncate it.
         if FullString'Last <= AuditTypes.UserTextI'Last then
            LocalUser (1.. FullString'Last) := FullString;
         else
            LocalUser := FullString (1 .. AuditTypes.UserTextI'Last);
         end if;

      return LocalUser;
   end ExtractUser;


   ------------------------------------------------------------------
   -- TheMechanism
   --
   -- Implementation Notes:
   --     None.
   ------------------------------------------------------------------

   function TheMechanism (Contents : ContentsT)
         return CryptoTypes.AlgorithmT
   is
   begin
      return Contents.Mechanism;
   end TheMechanism;


   ------------------------------------------------------------------
   -- IsCurrent
   --
   -- Implementation Notes:
   --     None.
   ------------------------------------------------------------------

   function IsCurrent (Contents : ContentsT) return Boolean
   is
   begin
       return
         Clock.GreaterThanOrEqual( Clock.TheCurrentTime, Contents.NotBefore) and
         Clock.LessThanOrEqual(Clock.TheCurrentTime, Contents.NotAfter);
   end IsCurrent;


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
      --# accept F, 10, Ignored, "Ineffective assignment expected here" &
      --#        F, 33, Ignored, "Ineffective assignment expected here";
      CertProcessing.ObtainRawData(RawCert => RawCert,
                                   RawData => LocalRawData,
                                   ObtainSuccess => Ignored);

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
      --# accept F, 10, Ignored, "Ineffective assignment expected here" &
      --#        F, 33, Ignored, "Ineffective assignment expected here";
      CertProcessing.ObtainSignatureData(RawCert => RawCert,
                                         SignatureData => LocalSig,
                                         ObtainSuccess => Ignored);

      return LocalSig;
   end GetSignature;


   ------------------------------------------------------------------
   -- IssuerKnown
   --
   -- Implementation Notes:
   --     None
   ------------------------------------------------------------------

   procedure IssuerKnown (Contents : in     ContentsT;
                          IsKnown   :    out Boolean )
   is
   begin

      KeyStore.KeyMatchingIssuerPresent
        ( Issuer    => Contents.ID.Issuer,
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
            ( Mechanism   => Contents.Mechanism,
              RawCertData => GetData(RawCert),
              Signature   => GetSignature(RawCert),
              TheIssuer   => Contents.ID.Issuer,
              Verified    => IsVerified);

       else
          IsVerified := False;
       end if;

   end IsOK;

end Cert;



