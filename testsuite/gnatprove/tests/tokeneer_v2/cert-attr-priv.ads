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
-- PrivCert
--
-- Description:
--    Defines the contents of a priv certificate.Certificates enter
--    the system as raw data, and are stored in an internally-defined
--    record structure.
--    Inherits the operations defined in AttrCert.
--
------------------------------------------------------------------

with Cert.Attr,
     CertTypes,
     PrivTypes;

package Cert.Attr.Priv is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   ------------------------------------------------------------------
   -- ContentsT
   --
   -- Description:
   --    Contents of a Priv certificate
   --
   -- Traceunit : C.PrivCert.Contents
   -- Traceto   : FD.Types.Certificates
   ------------------------------------------------------------------
   type ContentsT is private;


   ------------------------------------------------------------------
   -- TheRole
   --
   -- Description:
   --    Retrieves the subject's role
   --
   -- Traceunit : C.PrivCert.TheRole
   -- Traceto   : FD.Types.Certificates
   ------------------------------------------------------------------
   function TheRole (Contents : ContentsT) return PrivTypes.PrivilegeT;

   ------------------------------------------------------------------
   -- TheClearance
   --
   -- Description:
   --    Retrieves the subject's clearance
   --
   -- Traceunit : C.PrivCert.TheClearance
   -- Traceto   : FD.Types.Certificates
   ------------------------------------------------------------------
   function TheClearance (Contents : ContentsT) return PrivTypes.ClearanceT;

   ------------------------------------------------------------------
   -- Extract
   --
   -- Description:
   --    Extract the contents of a raw certificate.
   --
   -- Traceunit : C.PrivCert.Extract
   -- traceto: FD.Types.Certificates
   ------------------------------------------------------------------
   procedure Extract (RawCert  : in     CertTypes.RawCertificateT;
                      Contents :    out ContentsT;
                      Success  :    out Boolean)
     with Global  => null,
          Depends => ((Contents,
                       Success)  => RawCert);

   ------------------------------------------------------------------
   -- Clear
   --
   -- Description:
   --    Clears the contents of the certificate
   --
   -- Traceunit : C.PrivCert.Clear
   --
   ------------------------------------------------------------------
   procedure Clear (Contents :    out ContentsT)
     with Global  => null,
          Depends => (Contents => null);

   --  Converts the extended type to the original one.
   function Cert_Attr_Priv_To_Cert (Contents : in ContentsT)
                                   return Cert.ContentsT;

   function Cert_Attr_Priv_To_Cert_Attr (Contents : in ContentsT)
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

end Cert.Attr.Priv;
