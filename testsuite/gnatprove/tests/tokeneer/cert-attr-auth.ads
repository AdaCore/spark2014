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
-- AuthCert
--
-- Description:
--    Defines the contents of an auth certificate, and provides
--    operations on those contents.
--    Certificates enter the system as raw data, and are stored in
--    an internally-defined record structure.
--    Inherits the operations defined in AttrCert.
--
------------------------------------------------------------------

with CertTypes,
     Clock,
     Cert.Attr,
     PrivTypes;

use type PrivTypes.PrivilegeT;

package Cert.Attr.Auth is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   ------------------------------------------------------------------
   -- ContentsT
   --
   -- Description:
   --    Contents of an Auth certificate
   --
   -- Traceunit : C.Cert.Attr.Auth.Contents
   -- Traceto   : FD.Types.Certificates
   ------------------------------------------------------------------
   type ContentsT is private;

   ------------------------------------------------------------------
   -- TheRole
   --
   -- Description:
   --    Retrieves the subject's role
   --
   -- Traceunit : C.Cert.Attr.Auth.TheRole
   -- Traceto   : FD.Types.Certificates
   ------------------------------------------------------------------
   function TheRole (Contents : ContentsT) return PrivTypes.PrivilegeT
     with Global => null;

   ------------------------------------------------------------------
   -- TheClearance
   --
   -- Description:
   --    Retrieves the subject's clearance
   --
   -- Traceunit : C.Cert.Attr.Auth.TheClearance
   -- Traceto   : FD.Types.Certificates
   ------------------------------------------------------------------
   function TheClearance (Contents : ContentsT) return PrivTypes.ClearanceT
     with Global => null;

   ------------------------------------------------------------------
   -- Extract
   --
   -- Description:
   --    Extracts the contents of the certificate from the raw data.
   --
   -- Traceunit : C.Cert.Attr.Auth.Extract
   -- Traceto: FD.Types.Certificates
   ------------------------------------------------------------------
   procedure Extract (RawCert  : in     CertTypes.RawCertificateT;
                      Contents :    out ContentsT;
                      Success  :    out Boolean)
     with Global  => null,
          Depends => ((Contents,
                       Success)  => RawCert);

   ------------------------------------------------------------------
   -- Construct
   --
   -- Description:
   --    Constructs a raw certificate from the derived contents
   --
   -- Traceunit : C.Cert.Attr.Auth.Construct
   -- traceto: FD.Types.Certificates
   ------------------------------------------------------------------
   procedure Construct (Contents : in     ContentsT;
                        RawCert  :    out CertTypes.RawCertificateT)
     with Global  => null,
          Depends => (RawCert => Contents);

   ------------------------------------------------------------------
   -- SetContents
   --
   -- Description:
   --    Sets the fields of an auth certificate
   --
   -- Traceunit : C.Cert.Attr.Auth.SetContents
   -- traceto: FD.Certificate.NewAuthCert
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
     with Depends => (Contents => (BaseCertID,
                                   Clearance,
                                   ID,
                                   Mechanism,
                                   NotAfter,
                                   NotBefore,
                                   Role));

   ------------------------------------------------------------------
   -- IsOK
   --
   -- Description:
   --    (Overwrites inherited Cert.IsOK)
   --    Checks that the certificate is signed by this TIS.
   --
   -- Traceunit : C.Cert.Attr.Auth.IsOK
   -- Traceto: FD.Certificate.AuthCertSignedOK
   ------------------------------------------------------------------
   procedure IsOK (RawCert    : in     CertTypes.RawCertificateT;
                   Contents   : in     ContentsT;
                   IsVerified :    out Boolean)
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State,
                                 KeyStore.State,
                                 KeyStore.Store),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Contents,
                                               KeyStore.Store,
                                               RawCert),
                      IsVerified           => (Contents,
                                               KeyStore.State,
                                               KeyStore.Store,
                                               RawCert));

   ------------------------------------------------------------------
   -- Clear
   --
   -- Description:
   --    Clears the contents of the certificate
   --
   -- Traceunit : C.Cert.Attr.Auth.Clear
   --
   ------------------------------------------------------------------
   procedure Clear (Contents :    out ContentsT)
     with Global  => null,
          Depends => (Contents => null),
          Post    => TheRole(Contents) = PrivTypes.PrivilegeT'First;

   --  Converts the extended type to the original one.
   function Cert_Attr_Auth_To_Cert (Contents : in ContentsT)
                                   return Cert.ContentsT;

   --  Converts the extended type to the original one.
   function Cert_Attr_Auth_To_Cert_Attr (Contents : in ContentsT)
                                        return Cert.Attr.ContentsT;

private
   type ContentsT is record
      ID         : CertTypes.IDT;
      NotBefore  : Clock.TimeT;
      NotAfter   : Clock.TimeT;
      Mechanism  : CryptoTypes.AlgorithmT;
      BaseCertID : CertTypes.IDT;
      Role       : PrivTypes.PrivilegeT;
      Clearance  : PrivTypes.ClearanceT;
   end record;

   NullContents : constant ContentsT :=
     ContentsT'(ID         => CertTypes.NullID,
                NotBefore  => Clock.ZeroTime,
                NotAfter   => Clock.ZeroTime,
                Mechanism  => CryptoTypes.AlgorithmT'First,
                BaseCertID => CertTypes.NullID,
                Role       => PrivTypes.PrivilegeT'First,
                Clearance  => PrivTypes.ClearanceT'
                  (Class => PrivTypes.ClassT'First));

   ------------------------------------------------------------------
   -- TheRole
   --
   -- Implementation Notes:
   --     None
   ------------------------------------------------------------------

   function TheRole (Contents : ContentsT) return PrivTypes.PrivilegeT is
     (Contents.Role);


   ------------------------------------------------------------------
   -- TheClearance
   --
   -- Implementation Notes:
   --     None
   ------------------------------------------------------------------

   function TheClearance (Contents : ContentsT) return PrivTypes.ClearanceT is
     (Contents.Clearance);

end Cert.Attr.Auth;
