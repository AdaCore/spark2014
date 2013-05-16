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
with BasicTypes;
with CertTypes;
--# inherit AuditTypes,
--#         AuditLog,
--#         BasicTypes,
--#         CertTypes,
--#         Clock,
--#         ConfigData,
--#         File;

package CertificateStore
--# own State,
--#     FileState;
--# initializes FileState;
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

   procedure Init;
   --# global    out State;
   --#        in out FileState;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#        in     Clock.Now;
   --#        in     ConfigData.State;
   --# derives State,
   --#         FileState from FileState &
   --#         AuditLog.State from AuditLog.State,
   --#                             AuditLog.FileState,
   --#                             Clock.Now,
   --#                             ConfigData.State,
   --#                             FileState &
   --#         AuditLog.FileState from AuditLog.State,
   --#                             AuditLog.FileState,
   --#                             ConfigData.State,
   --#                             Clock.Now,
   --#                             FileState;


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

   procedure UpdateStore;
   --# global in out State;
   --#        in out FileState;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#        in     Clock.Now;
   --#        in     ConfigData.State;
   --# derives State     from State &
   --#         FileState from State,
   --#                        FileState &
   --#         AuditLog.State from AuditLog.State,
   --#                             AuditLog.FileState,
   --#                             Clock.Now,
   --#                             ConfigData.State,
   --#                             State,
   --#                             FileState &
   --#         AuditLog.FileState from AuditLog.State,
   --#                             AuditLog.FileState,
   --#                             ConfigData.State,
   --#                             Clock.Now,
   --#                             State,
   --#                             FileState;


   ------------------------------------------------------------------
   -- SerialNumberHasOverflowed
   --
   -- Description:
   --    Returns true if the last valid serial number has been used.
   --
   ------------------------------------------------------------------

   function SerialNumberHasOverflowed return Boolean;
   --# global State;


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

   function SerialNumber return CertTypes.SerialNumberT;
   --# global State;
   --# pre not SerialNumberHasOverflowed(State);


end CertificateStore;
