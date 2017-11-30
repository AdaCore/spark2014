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
   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------

   type LogFileStateT (<>) is private;

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
                      State     => (ConfigData.State,
                                    FileState));

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
   procedure AddElementToLog (ElementID   : in     AuditTypes.ElementT;
                              Severity    : in     AuditTypes.SeverityT;
                              User        : in     AuditTypes.UserTextT;
                              Description : in     String)
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State),
                      In_Out => (FileState,
                                 State)),
          Depends => ((FileState,
                       State)     => (Clock.Now,
                                      ConfigData.State,
                                      Description,
                                      ElementID,
                                      FileState,
                                      Severity,
                                      State,
                                      User)),
          Pre     => Description'First = 1;

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
          Depends => (Archive     => (FileState,
                                      State),
                      (FileState,
                       State)     => (Clock.Now,
                                      ConfigData.State,
                                      FileState,
                                      State,
                                      User));

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
                       State)     => (Clock.Now,
                                      ConfigData.State,
                                      FileState,
                                      State,
                                      User));

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
     with Global => State;

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
     with Global => State;

private
   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------

   MaxNumberLogFiles : constant := 2**4 + 1;  -- 17
   MaxNumberArchivableFiles : constant := 4;

   type LogFileCountT is range 0..MaxNumberLogFiles;
   subtype LogFileIndexT is LogFileCountT range 1..MaxNumberLogFiles;

   type FileStatusT is (Free, Archived, Used);

   type LogFilesT is array (LogFileIndexT) of File.T;

   type LogFilesStatusT is array (LogFileIndexT) of FileStatusT;

   subtype FileNameI is Positive range 1..16;
   subtype FileNameT is String(FileNameI);

   type LogFileNamesT is array (LogFileIndexT) of FileNameT;

   type LogFileListEntriesT is array (LogFileIndexT) of LogFileIndexT;

   ----------------------------------------------------------------
   -- LogFileListT
   --
   -- Description:
   --   This represents a list.
   --      List - is a cyclic buffer that can hold all the files
   --      Head - is the current head of the list in the cyclic buffer
   --      LastI - is the last index of the list in the cyclic buffer
   --      Length - is the length of the list
   --   The values of Head and LastI are not significant when Length=0.
   -----------------------------------------------------------------

   type LogFileListT is record
      List   : LogFileListEntriesT;
      Head   : LogFileIndexT;
      LastI  : LogFileIndexT;
      Length : LogFileCountT;
   end record;

   EmptyList : constant LogFileListT :=
     LogFileListT'(List => LogFileListEntriesT'
                               (others => LogFileIndexT'First),
                   Head => LogFileIndexT'Last,
                   LastI => LogFileIndexT'First,
                   Length => 0);


   subtype LogDirStringI is Positive range 1..3;
   subtype LogDirStringT is String(LogDirStringI);

   LogDirectory : constant LogDirStringT := "Log";

   subtype ArchiveFileStringI is Positive range 1..17;
   subtype ArchiveFileStringT is String(ArchiveFileStringI);

   ArchiveFileName : constant ArchiveFileStringT := "./Log/archive.log";

   --------------------------------------------------------------
   --  ElementText
   --
   --  Description:
   --     Text representation of Element name
   --
   --------------------------------------------------------------
   subtype ElementTextI is Positive range 1..20;
   subtype ElementTextT is String(ElementTextI);

   NoElement : constant ElementTextT := ElementTextT'(others => ' ');

   ------------------------------------------------------------------
   -- MaxLogFileEntries
   --
   --  Description:
   --     The max number of entries in a file.
   --     Note that it is a requirement of the Formal Design that
   --        MaxLogFileEntries * (NumberLogFiles - 1)
   --                                * AuditTypes.SizeAuditElement
   --             >= AuditTypes.MaxSupportedLogSize
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   MaxLogFileEntries : constant :=
     AuditTypes.MaxSupportedLogEntries/(MaxNumberLogFiles - 1);
   MaxLogEntries     : constant := MaxLogFileEntries * MaxNumberLogFiles;

   type LogEntryCountT is range 0..MaxLogEntries;
   subtype FileEntryCountT is LogEntryCountT range 0..MaxLogFileEntries;

   type LogFileEntryT is array (LogFileIndexT) of FileEntryCountT;

   ------------------------------------------------------------------
   -- State
   --
   ------------------------------------------------------------------
   function Valid_NumberLogEntries (CurrentLogFile   : LogFileIndexT;
                                    NumberLogEntries : LogEntryCountT;
                                    UsedLogFiles     : LogFileListT;
                                    LogFileEntries   : LogFileEntryT)
                                    return Boolean is
     (UsedLogFiles.Length >= 1 and then
        NumberLogEntries =
          LogEntryCountT(UsedLogFiles.Length - 1) * MaxLogFileEntries +
          LogFileEntries(CurrentLogFile))
      with Ghost;

   type LogFileStateT is record
      CurrentLogFile   : LogFileIndexT  := 1;
      NumberLogEntries : LogEntryCountT := 0;
      UsedLogFiles     : LogFileListT   :=
        LogFileListT'(List   => (others => 1),
                      Head   => 1,
                      LastI  => 1,
                      Length => 1);
      LogFileEntries   : LogFileEntryT  := (others => 0);
   end record
     with Type_Invariant =>
       Valid_NumberLogEntries
         (CurrentLogFile, NumberLogEntries, UsedLogFiles, LogFileEntries);

   function Valid_NumberLogEntries (LogFileState : LogFileStateT) return Boolean is
     (Valid_NumberLogEntries (LogFileState.CurrentLogFile,
                              LogFileState.NumberLogEntries,
                              LogFileState.UsedLogFiles,
                              LogFileState.LogFileEntries))
   with Ghost;

   LogFiles         : LogFilesT := LogFilesT'(others => File.NullFile)
     with Part_Of => FileState;

   LogFilesStatus   : LogFilesStatusT with Part_Of => State;
   LogFileState     : LogFileStateT with Part_Of => State;
   AuditAlarm       : AlarmTypes.StatusT with Part_Of => State;

   AuditSystemFault : Boolean with Part_Of => State;

end AuditLog;
