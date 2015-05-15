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

with AdminToken,
     AuditLog,
     AuditTypes,
     Clock,
     ConfigData,
     File,
     IandATypes,
     PrivTypes;

package Configuration is

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
   procedure Init
     with Global  => (Output => ConfigData.State,
                      In_Out => ConfigData.FileState),
          Depends => ((ConfigData.FileState,
                       ConfigData.State)     => ConfigData.FileState);

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
     (TheFile   : in out File.T;
      DataValid :    out Boolean)
     with Global  => (Input  => (AdminToken.State,
                                 Clock.Now),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 ConfigData.FileState,
                                 ConfigData.State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)       => (AdminToken.State,
                                                 AuditLog.FileState,
                                                 AuditLog.State,
                                                 Clock.Now,
                                                 ConfigData.FileState,
                                                 ConfigData.State,
                                                 TheFile),
                      (ConfigData.FileState,
                       ConfigData.State,
                       TheFile)              =>+ TheFile,
                      DataValid              => TheFile);


end Configuration;
