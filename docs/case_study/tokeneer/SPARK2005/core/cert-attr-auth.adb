------------------------------------------------------------------
-- Tokeneer ID Station Core Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency. All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd. under contract to the National Security Agency.
--
-- Modifications to proof annotations by Phil Thornley, April 2009
------------------------------------------------------------------

------------------------------------------------------------------
-- AuthCert
--
-- Implementation Notes:
--     None
--
------------------------------------------------------------------
with CertProcessing,
     BasicTypes,
     KeyStore;

use type BasicTypes.Unsigned32T;

package body Cert.Attr.Auth is


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
      LocalContents : CertProcessing.AuthCertDataT;
      Extracted,
      NotBeforeOk,
      NotAfterOk    : Boolean;
   begin
      CertProcessing.ExtractAuthCertData(RawAuthCert    => RawCert,
                                         AuthCert       => LocalContents,
                                         ExtractSuccess => Extracted);

      Contents.ID.Issuer       := LocalContents.Issuer;
      Contents.ID.SerialNumber
        := CertTypes.SerialNumberT(LocalContents.SerialNumber);
      Contents.Mechanism       := LocalContents.SigAlgID;
      Contents.BaseCertID      := LocalContents.Holder;
      Contents.Role            := LocalContents.Privilege.Role;
      Contents.Clearance.Class := LocalContents.Privilege.Class;

      -- NotBefore and NotAfter are read as unsigned 32 bit words -
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
   -- Construct
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure Construct (Contents : in     ContentsT;
                        RawCert  :    out CertTypes.RawCertificateT)
   is
      LocalContents : CertProcessing.AuthCertDataT;

      ------------------------------------------------------------------
      -- ConvertTISTime
      --
      -- Description:
      --    Converts a TIS time value into a raw time value
      --
      -- Implementation Notes:
      --    Uses Clock.SplitTime
      ------------------------------------------------------------------
      procedure ConvertTISTime(Time : in     Clock.TimeT;
                               Raw  :    out CertProcessing.TimeT)
      --# derives Raw from Time;
      is
         TheYear   : Clock.YearsT;
         TheMonth  : Clock.MonthsT;
         TheDay    : Clock.DaysT;
         TheHour   : Clock.HoursT;
         TheMinute : Clock.MinutesT;
      begin
         Clock.SplitTime(TheTime => Time,
                         Year    => TheYear,
                         Month   => TheMonth,
                         Day     => TheDay,
                         Hour    => TheHour,
                         Min     => TheMinute);
         Raw := CertProcessing.TimeT'(
                   Year   => BasicTypes.Unsigned32T(TheYear),
                   Month  => BasicTypes.Unsigned32T(TheMonth),
                   Day    => BasicTypes.Unsigned32T(TheDay),
                   Hour   => BasicTypes.Unsigned32T(TheHour),
                   Minute => BasicTypes.Unsigned32T(TheMinute));
      end ConvertTISTime;

   begin
      LocalContents.Issuer          := Contents.ID.Issuer;
      LocalContents.SerialNumber
        := BasicTypes.Unsigned32T(Contents.ID.SerialNumber);
      LocalContents.SigAlgID        := Contents.Mechanism;
      LocalContents.Holder          := Contents.BaseCertID;
      LocalContents.Privilege.Role  := Contents.Role;
      LocalContents.Privilege.Class := Contents.Clearance.Class;

      ConvertTISTime(Contents.NotBefore,
                     LocalContents.AttCertValidity.NotBefore);
      ConvertTISTime(Contents.NotAfter,
                     LocalContents.AttCertValidity.NotAfter);

      CertProcessing.ConstructAuthCert(
                        AuthCert            => LocalContents,
                        UnsignedRawAuthCert => RawCert);
   end Construct;


   ------------------------------------------------------------------
   -- SetContents
   --
   -- Implementation Notes:
   --     None
   ------------------------------------------------------------------
   procedure SetContents
     (ID         : in     CertTypes.IDT;
      NotBefore  : in     Clock.TimeT;
      NotAfter   : in     Clock.TimeT;
      Mechanism  : in     CryptoTypes.AlgorithmT;
      BaseCertID : in     CertTypes.IDT;
      Role       : in     PrivTypes.PrivilegeT;
      Clearance  : in     PrivTypes.ClearanceT;
      Contents   :    out ContentsT)
   is
   begin
      Contents.ID         := ID;
      Contents.NotBefore  := NotBefore;
      Contents.NotAfter   := NotAfter;
      Contents.Mechanism  := Mechanism;
      Contents.BaseCertID := BaseCertID;
      Contents.Role       := Role;
      Contents.Clearance  := Clearance;
   end SetContents;


   ------------------------------------------------------------------
   -- IsOK
   --
   -- Implementation Notes:
   --     None
   ------------------------------------------------------------------
   procedure IsOK (RawCert    : in     CertTypes.RawCertificateT;
                   Contents   : in     ContentsT;
                   IsVerified :    out Boolean)
   is
   begin

      Cert.IsOK (RawCert => RawCert,
                 Contents => Cert.ContentsT(Contents),
                 IsVerified => IsVerified);

      IsVerified := IsVerified
                    and KeyStore.IssuerIsThisTIS(Contents.ID.Issuer);

   end IsOK;


   ------------------------------------------------------------------
   -- Clear
   --
   -- Implementation Notes:
   --     None
   ------------------------------------------------------------------
   procedure Clear (Contents :    out ContentsT)
   is
      --# for NullContents declare Rule;
   begin
      Contents := NullContents;
   end Clear;

end Cert.Attr.Auth;
