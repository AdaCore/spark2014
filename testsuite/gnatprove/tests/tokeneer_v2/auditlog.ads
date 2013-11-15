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
-- AuditLog
--
-- Description:
--    Provides facilities to add elements to the audit log.
--
------------------------------------------------------------------
with AlarmTypes,
     AuditTypes,
     Clock,
     ConfigData,
     File;

package AuditLog
  with Abstract_State => (FileState,
                          State),
       Initializes    => FileState
is
   --  Helper expression function that acts as the precondition of
   --  AddElementToLog, ArchiveLog and ClearLogEntries. It allows us
   --  to refer to types and variables that are declared in the body
   --  and are not visible here and it acts as an invariant.
   function Valid_NumberLogEntries return Boolean
     with Global => State;

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------

   ------------------------------------------------------------------
   -- Init
   --
   -- Description:
   --    Initialises the audit log.
   --    Brings back persistent state from file, hence implements most
   --    of AddElementsToLog in TISStartup (i.e.the Xi part)
   --
   -- Traceunit : C.AuditLog.Init
   -- Traceto   : FD.TIS.TISStartup
   ------------------------------------------------------------------
   procedure Init
     with Global  => (Input  => ConfigData.State,
                      Output => State,
                      In_Out => FileState),
          Depends => (FileState =>+ null,
                      State => (ConfigData.State,
                                FileState)),
          Post    => Valid_NumberLogEntries;

   ------------------------------------------------------------------
   -- AddElementToLog
   --
   -- Description:
   --    Determines whether log files are full.If so truncate
   --    oldest log, add truncElement, and add new element (component
   --    parts passed as parameters) to the truncated log.Raises alarm
   --    if number of logs is beyond the alarm threshold.
   --
   -- Traceunit : C.AuditLog.AddElementToLog
   -- Traceto   : FD.AuditLog.AddElementToLog
   ------------------------------------------------------------------
   procedure AddElementToLog (
                ElementID   : in     AuditTypes.ElementT;
                Severity    : in     AuditTypes.SeverityT;
                User        : in     AuditTypes.UserTextT;
                Description : in     String)
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State),
                      In_Out => (FileState,
                                 State)),
          Depends => ((FileState,
                       State) => (Clock.Now,
                                  ConfigData.State,
                                  Description,
                                  ElementID,
                                  FileState,
                                  Severity,
                                  State,
                                  User)),
          Pre     => Valid_NumberLogEntries and Description'First = 1,
          Post    => Valid_NumberLogEntries;

   ------------------------------------------------------------------
   -- ArchiveLog
   --
   -- Description:
   --    Determines the log files to be archived, and marks them as such.
   --    adds an archiveLogElement to the log.
   --
   -- Traceunit : C.AuditLog.ArchiveLog
   -- Traceto   : FD.AuditLog.ArchiveLog
   ------------------------------------------------------------------
   procedure ArchiveLog (User    : in     AuditTypes.UserTextT;
                         Archive :    out File.T)
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State),
                      In_Out => (FileState,
                                 State)),
          Depends => (Archive => (FileState,
                                  State),
                      (FileState,
                       State) => (Clock.Now,
                                  ConfigData.State,
                                  FileState,
                                  State,
                                  User)),
          Pre     => Valid_NumberLogEntries,
          Post    => Valid_NumberLogEntries;

   ------------------------------------------------------------------
   -- ClearLogEntries
   --
   -- Description:
   --    Clears the log files marked as Archive.
   --    Adds an archiveCompleteElement to the log.
   --
   -- Traceunit : C.AuditLog.ClearLogEntries
   -- Traceto   : FD.AuditLog.ClearLog
   ------------------------------------------------------------------
   procedure ClearLogEntries (User : in     AuditTypes.UserTextT)
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State),
                      In_Out => (FileState,
                                 State)),
          Depends => ((FileState,
                       State) => (Clock.Now,
                                  ConfigData.State,
                                  FileState,
                                  State,
                                  User)),
          Pre     => Valid_NumberLogEntries,
          Post    => Valid_NumberLogEntries;

   ------------------------------------------------------------------
   -- CancelArchive
   --
   -- Description:
   --    Reverts the log files marked as Archive back to Used.
   --
   -- Traceunit : C.AuditLog.CancelArchive
   -- Traceto   : FD.AuditLog.CancelArchive
   ------------------------------------------------------------------
   procedure CancelArchive
     with Global  => (In_Out => State),
          Depends => (State =>+ null);

   ------------------------------------------------------------------
   -- TheAuditAlarm
   --
   -- Description:
   --    Returns the current state of the alarm.
   --
   -- traceunit : C.AuditLog.TheAuditAlarm
   -- traceto   : FD.AuditLog.State
   ------------------------------------------------------------------
   function TheAuditAlarm return AlarmTypes.StatusT
     with Global  => State;

   ------------------------------------------------------------------
   -- SystemFaultOccurred
   --
   -- Description:
   --    Returns True exactly when a critical system fault has occurred
   --    while attempting to maintain the audit log.
   --
   -- traceunit : C.AuditLog.SystemFaultOccurred
   ------------------------------------------------------------------
   function SystemFaultOccurred return Boolean
     with Global  => State;

end AuditLog;
