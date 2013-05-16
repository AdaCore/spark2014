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
-- AttrCert
--
-- Description:
--    Defines the common contents of an attribute certificate,
--    and operations on those contents.
--    Certificates enter the system as raw data, and are stored in
--    an internally-defined record structure.
--    Inherits the operations defined in Cert.
--
------------------------------------------------------------------

with AuditTypes,
     Cert,
     CertTypes;

--# inherit AuditTypes,
--#         Cert,
--#         CertTypes;

package Cert.Attr is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   ------------------------------------------------------------------
   -- ContentsT
   --
   -- Description:
   --    Contents common to all attribute certificates
   --
   -- Traceunit : C.AttrCert.Contents
   -- Traceto   : FD.Types.Certificates
   ------------------------------------------------------------------
   type ContentsT is new Cert.ContentsT with private;


   ------------------------------------------------------------------
   -- ExtractUser
   --
   -- Description:
   --    Returns the user info as a string
   --    Overrides ExtractUser operation in Cert.
   --
   -- Traceunit : C.Cert.ExtractUser
   -- Traceto   : FD.AuditLog.ExtractUser
   ------------------------------------------------------------------

   function ExtractUser (Contents : ContentsT) return AuditTypes.UserTextT;

   ------------------------------------------------------------------
   -- TheBaseCert
   --
   -- Description:
   --    Retrieves the Base Certificate ID.
   --
   -- Traceunit : C.AttrCert.TheBaseCert
   -- Traceto   : FD.Types.Certificates
   ------------------------------------------------------------------

   function TheBaseCert (Contents : ContentsT) return CertTypes.IDT;


   private
      type ContentsT is new Cert.ContentsT with
         record
            BaseCertID : CertTypes.IDT;
         end record;

     NullContents : constant ContentsT :=
       ContentsT'( Cert.NullContents with
                   BaseCertID   => CertTypes.NullID);


--# accept W, 394, ContentsT, "Child packages supply constructors for ContentsT";
end Cert.Attr;
