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
-- Configuration
--
-- Description:
--    Utility package for interacting with the configuration data.
--
------------------------------------------------------------------

with File;
--# inherit
--#    Clock,
--#    AuditTypes,
--#    AuditLog,
--#    AdminToken,
--#    PrivTypes,
--#    IandATypes,
--#    File,
--#    ConfigData;


package Configuration
is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   ------------------------------------------------------------------
   -- Init
   --
   -- Description:
   --      Initialises the configuration data. Takes the data from file
   --      if it can.
   --
   -- Traceunit: C.Configuration.Init
   -- Traceto: FD.TIS.TISStartup
   -- Traceto: FD.TIS.InitIDStation
   ------------------------------------------------------------------
   procedure Init;
   --# global in out ConfigData.FileState;
   --#           out ConfigData.State;
   --# derives ConfigData.State,
   --#         ConfigData.FileState from ConfigData.FileState;

   ------------------------------------------------------------------
   -- UpdateData
   --
   -- Description:
   --      Updates the configuration data.
   --      Performs all auditing of the configuration data update
   --      May raise UpdatedConfigData
   --                InvalidConfigData
   --                SystemFault.
   --
   -- Traceunit: C.Configuration.UpdateData
   -- Traceto: FD.Enclave.FinishUpdateConfigDataOK
   -- Traceto: FD.Enclave.FinishUpdateConfigDataFail
   ------------------------------------------------------------------
   procedure UpdateData
     (TheFile        : in out File.T;
      DataValid      :    out Boolean);
   --# global in     AdminToken.State;
   --#        in     Clock.Now;
   --#        in out ConfigData.State;
   --#        in out ConfigData.FileState;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --# derives ConfigData.State,
   --#         ConfigData.FileState,
   --#         TheFile              from *,
   --#                                   TheFile &
   --#         DataValid            from TheFile &
   --#         AuditLog.State,
   --#         AuditLog.FileState   from ConfigData.State,
   --#                                   ConfigData.FileState,
   --#                                   AuditLog.State,
   --#                                   AuditLog.FileState,
   --#                                   AdminToken.State,
   --#                                   TheFile,
   --#                                   Clock.Now;


end Configuration;



