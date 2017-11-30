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
-- CertificateStore
--
-- Description:
--    Maintains the certificate store
--
------------------------------------------------------------------
with AuditLog,
     AuditTypes,
     CommonTypes,
     CertTypes,
     Clock,
     ConfigData,
     File;

package CertificateStore
  with Abstract_State => (FileState,
                          State),
       Initializes    => FileState
is

   ------------------------------------------------------------------
   -- Init
   --
   -- Description:
   --    Initializes the certificate store from persistent state
   --    held on file.
   --    Raises a system fault (warning severity) if the file cannot
   --    be read.
   --
   -- Traceunit : C.CertificateStore.Init
   -- Traceto   : FD.TIS.TISStartup
   ------------------------------------------------------------------
   procedure Init
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State),
                      Output => State,
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 FileState)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               FileState),
                      (FileState,
                       State)              => FileState);

   ------------------------------------------------------------------
   -- UpdateStore
   --
   -- Description:
   --    Updates the value held in the certificate store.
   --    Raise a system fault (warning severity) if the file cannot
   --    be written to.
   --
   -- traceunit : C.CertificateStore.UpdateStore
   -- traceto   : FD.CertificateStore.Update
   ------------------------------------------------------------------
   procedure UpdateStore
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 FileState,
                                 State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               FileState,
                                               State),
                      (FileState,
                       State)              =>+ State);

   ------------------------------------------------------------------
   -- SerialNumberHasOverflowed
   --
   -- Description:
   --    Returns true if the last valid serial number has been used.
   --
   ------------------------------------------------------------------
   function SerialNumberHasOverflowed return Boolean
     with Global => State;

   ------------------------------------------------------------------
   -- SerialNumber
   --
   -- Description:
   --    Obtains the next available serial number from certificate
   --    store
   --
   -- traceunit : C.CertificateStore.SerialNumber
   -- traceto   : FD.CertificateStore.State
   ------------------------------------------------------------------
   function SerialNumber return CertTypes.SerialNumberT
     with Global => State,
          Pre    => not SerialNumberHasOverflowed;

end CertificateStore;
