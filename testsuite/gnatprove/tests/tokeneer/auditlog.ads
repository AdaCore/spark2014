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
-- AuditLog
--
-- Description:
--    Provides facilities to add elements to the audit log.
--
------------------------------------------------------------------
with AlarmTypes,
     AuditTypes,
     File;
--# inherit AuditTypes,
--#         AlarmTypes,
--#         Clock,
--#         ConfigData,
--#         File;

package AuditLog
--# own State,
--#     FileState;
--# initializes FileState;
is

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
   --    of AddElementsToLog in TISStartup (i.e. the Xi part)
   --
   -- Traceunit : C.AuditLog.Init
   -- Traceto   : FD.TIS.TISStartup
   ------------------------------------------------------------------

   procedure Init;
   --# global in     ConfigData.State;
   --#        in out FileState;
   --#           out State;
   --# derives FileState from * &
   --#         State     from FileState,
   --#                        ConfigData.State;

   ------------------------------------------------------------------
   -- AddElementToLog
   --
   -- Description:
   --    Determines whether log files are full. If so truncate
   --    oldest log, add truncElement, and add new element (component
   --    parts passed as parameters) to the truncated log. Raises alarm
   --    if number of logs is beyond the alarm threshold.
   --
   -- Traceunit : C.AuditLog.AddElementToLog
   -- Traceto   : FD.AuditLog.AddElementToLog
   ------------------------------------------------------------------

   procedure AddElementToLog (
                ElementID    : in     AuditTypes.ElementT;
                Severity     : in     AuditTypes.SeverityT;
                User         : in     AuditTypes.UserTextT;
                Description  : in     String);
   --# global in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in out FileState;
   --#        in out State;
   --# derives FileState,
   --#         State     from FileState,
   --#                        State,
   --#                        ConfigData.State,
   --#                        ElementID,
   --#                        Severity,
   --#                        User,
   --#                        Description,
   --#                        Clock.Now;


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
                         Archive :    out File.T);
   --# global in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in out FileState;
   --#        in out State;
   --# derives FileState,
   --#         State     from FileState,
   --#                        State,
   --#                        ConfigData.State,
   --#                        User,
   --#                        Clock.Now &
   --#         Archive   from FileState,
   --#                        State;


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

   procedure ClearLogEntries (User    : in     AuditTypes.UserTextT);
   --# global in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in out FileState;
   --#        in out State;
   --# derives FileState,
   --#         State     from FileState,
   --#                        State,
   --#                        ConfigData.State,
   --#                        User,
   --#                        Clock.Now;


   ------------------------------------------------------------------
   -- CancelArchive
   --
   -- Description:
   --    Reverts the log files marked as Archive back to Used.
   --
   -- Traceunit : C.AuditLog.CancelArchive
   -- Traceto   : FD.AuditLog.CancelArchive
   ------------------------------------------------------------------

   procedure CancelArchive;
   --# global in out State;
   --# derives State from *;

   ------------------------------------------------------------------
   -- TheAuditAlarm
   --
   -- Description:
   --    Returns the current state of the alarm.
   --
   -- traceunit : C.AuditLog.TheAuditAlarm
   -- traceto   : FD.AuditLog.State
   ------------------------------------------------------------------
   function TheAuditAlarm return AlarmTypes.StatusT;
   --# global State;

   ------------------------------------------------------------------
   -- SystemFaultOccurred
   --
   -- Description:
   --    Returns True exactly when a critical system fault has occurred
   --    while attempting to maintain the audit log.
   --
   -- traceunit : C.AuditLog.SystemFaultOccurred
   ------------------------------------------------------------------
   function SystemFaultOccurred return Boolean;
   --# global State;

end AuditLog;
