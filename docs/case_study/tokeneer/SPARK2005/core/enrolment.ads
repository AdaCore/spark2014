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
     AuditTypes;

--# inherit Cert.ID,
--#         CertTypes,
--#         CryptoTypes,
--#         ConfigData,
--#         AuditTypes,
--#         AuditLog,
--#         KeyStore,
--#         Clock,
--#         File;

package Enrolment
is

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
                       Description :    out AuditTypes.DescriptionT);
   --# global in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in out KeyStore.Store;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#        in out KeyStore.State;
   --# derives DataOK,
   --#         TheFile,
   --#         Description,
   --#         KeyStore.Store     from TheFile,
   --#                                 KeyStore.Store &
   --#         AuditLog.State,
   --#         AuditLog.FileState from TheFile,
   --#                                 KeyStore.Store,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 ConfigData.State,
   --#                                 Clock.Now &
   --#         KeyStore.State     from *,
   --#                                 TheFile,
   --#                                 KeyStore.Store;
   --# pre not KeyStore.PrivateKeyPresent(KeyStore.State);
   --# post DataOK <->
   --#      KeyStore.PrivateKeyPresent(KeyStore.State);

end Enrolment;
