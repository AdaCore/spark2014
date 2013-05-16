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
--# inherit AuditTypes,
--#         AuditLog,
--#         BasicTypes,
--#         Cert.Attr,
--#         CertProcessing,
--#         CertTypes,
--#         CryptoTypes,
--#         Clock,
--#         ConfigData,
--#         PrivTypes,
--#         KeyStore;

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
   type ContentsT is new Attr.ContentsT with private;


   ------------------------------------------------------------------
   -- TheRole
   --
   -- Description:
   --    Retrieves the subject's role
   --
   -- Traceunit : C.Cert.Attr.Auth.TheRole
   -- Traceto   : FD.Types.Certificates
   ------------------------------------------------------------------

   function TheRole (Contents : ContentsT) return PrivTypes.PrivilegeT;


   ------------------------------------------------------------------
   -- TheClearance
   --
   -- Description:
   --    Retrieves the subject's clearance
   --
   -- Traceunit : C.Cert.Attr.Auth.TheClearance
   -- Traceto   : FD.Types.Certificates
   ------------------------------------------------------------------

   function TheClearance (Contents : ContentsT) return PrivTypes.ClearanceT;

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
                      Success  :    out Boolean);
   --# derives Contents,
   --#         Success  from RawCert;


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
                        RawCert  :    out CertTypes.RawCertificateT);
   --# derives RawCert from Contents;


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
      Contents   :    out ContentsT);
   --# derives Contents from ID,
   --#                       NotBefore,
   --#                       NotAfter,
   --#                       Mechanism,
   --#                       BaseCertID,
   --#                       Role,
   --#                       Clearance;


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
                   IsVerified :    out Boolean);
   --# global in     KeyStore.Store;
   --#        in     KeyStore.State;
   --#        in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out AuditLog.FileState;
   --#        in out AuditLog.State;
   --# derives AuditLog.FileState,
   --#         AuditLog.State     from Contents,
   --#                                 RawCert,
   --#                                 KeyStore.Store,
   --#                                 AuditLog.FileState,
   --#                                 AuditLog.State,
   --#                                 Clock.Now,
   --#                                 ConfigData.State &
   --#         IsVerified         from Contents,
   --#                                 RawCert,
   --#                                 KeyStore.Store,
   --#                                 KeyStore.State;

   ------------------------------------------------------------------
   -- Clear
   --
   -- Description:
   --    Clears the contents of the certificate
   --
   -- Traceunit : C.Cert.Attr.Auth.Clear
   --
   ------------------------------------------------------------------
   procedure Clear (Contents :    out ContentsT);
   --# derives Contents from ;
   --# post TheRole(Contents) = PrivTypes.PrivilegeT'First;


   private
      type ContentsT is new Attr.ContentsT with
         record
            Role      : PrivTypes.PrivilegeT;
            Clearance : PrivTypes.ClearanceT;
         end record;

     NullContents : constant ContentsT :=
       ContentsT'( Attr.NullContents with
                   Role      => PrivTypes.PrivilegeT'First,
                   Clearance => PrivTypes.ClearanceT'
                                      (Class => PrivTypes.ClassT'First));


end Cert.Attr.Auth;
