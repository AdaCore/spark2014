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
-- Enrolment
--
-- Description:
--    Utility package providing Enrolment validation.
--
------------------------------------------------------------------

with File,
     AuditLog,
     AuditTypes,
     Cert.ID,
     CertTypes,
     Clock,
     ConfigData,
     CryptoTypes,
     File,
     KeyStore;

use KeyStore;

package Enrolment is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------


   ------------------------------------------------------------------
   -- Validate
   --
   -- Description:
   --    Performs the required validation checks on the enrolment
   --    data read from the floppy.
   --    If the data on the floppy is acceptable to be used for
   --    enrolment then the Key store is updated.
   --
   -- Traceunit : C.Enrolment.Validate
   -- Traceto : FD.Enclave.ValidateEnrolmentDataOK
   -- Traceto : FD.Enclave.ValidateEnrolmentDataFail
   -- Traceto : FD.KeyStore.UpdateKeyStore
   ------------------------------------------------------------------
   procedure Validate (TheFile     : in out File.T;
                       DataOK      :    out Boolean;
                       Description :    out AuditTypes.DescriptionT)
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 KeyStore.State,
                                 KeyStore.Store)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               KeyStore.Store,
                                               TheFile),
                      (DataOK,
                       Description,
                       KeyStore.Store,
                       TheFile)            => (KeyStore.Store,
                                               TheFile),
                      KeyStore.State       =>+ (KeyStore.Store,
                                                TheFile)),
          Pre     => not KeyStore.PrivateKeyPresent,
          Post    => DataOK = KeyStore.PrivateKeyPresent;

end Enrolment;
