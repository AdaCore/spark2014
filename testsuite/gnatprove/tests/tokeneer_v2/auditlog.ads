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
--# inherit AlarmTypes,  AuditTypes,  Clock,  ConfigData,  File;

package AuditLog
   with Abstract_State => (FileState,
                           State)
--# initializes FileState;
is

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
       List : LogFileListEntriesT;
       Head : LogFileIndexT;
       LastI : LogFileIndexT;
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
   MaxLogFileEntries : constant
     := AuditTypes.MaxSupportedLogEntries/(MaxNumberLogFiles - 1);
   MaxLogEntries     : constant := MaxLogFileEntries * MaxNumberLogFiles;

   type LogEntryCountT  is range 0..MaxLogEntries;
   subtype FileEntryCountT is LogEntryCountT range 0..MaxLogFileEntries;

   type LogFileEntryT is array (LogFileIndexT) of FileEntryCountT;


   ------------------------------------------------------------------
   -- State
   --
   ------------------------------------------------------------------
   LogFiles : LogFilesT := LogFilesT'(others => File.NullFile);

   CurrentLogFile : LogFileIndexT;
   LogFilesStatus : LogFilesStatusT;
   NumberLogEntries : LogEntryCountT;
   UsedLogFiles : LogFileListT;
   LogFileEntries : LogFileEntryT;

   AuditAlarm : AlarmTypes.StatusT;

   AuditSystemFault : Boolean;
   ------------------------------------------------------------------
   -- LogFileNames
   --
   -- Description:
   --       A look-up table giving file names.
   --
   ------------------------------------------------------------------
   LogFileNames : constant LogFileNamesT :=
     LogFileNamesT'(1 => "./Log/File01.log",
                    2 => "./Log/File02.log",
                    3 => "./Log/File03.log",
                    4 => "./Log/File04.log",
                    5 => "./Log/File05.log",
                    6 => "./Log/File06.log",
                    7 => "./Log/File07.log",
                    8 => "./Log/File08.log",
                    9 => "./Log/File09.log",
                    10 => "./Log/File10.log",
                    11 => "./Log/File11.log",
                    12 => "./Log/File12.log",
                    13 => "./Log/File13.log",
                    14 => "./Log/File14.log",
                    15 => "./Log/File15.log",
                    16 => "./Log/File16.log",
                    17 => "./Log/File17.log"
                   );



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
           Post    => (UsedLogFiles.Length >= 1 and then
                         NumberLogEntries =
                         LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
                         LogFileEntries(CurrentLogFile));

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
                ElementID    : in     AuditTypes.ElementT;
                Severity     : in     AuditTypes.SeverityT;
                User         : in     AuditTypes.UserTextT;
                Description  : in     String)
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
           Pre     => (UsedLogFiles.Length >= 1 and then
                         NumberLogEntries =
                         LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
                         LogFileEntries(CurrentLogFile)),
           Post     => (UsedLogFiles.Length >= 1 and then
                         NumberLogEntries =
                         LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
                         LogFileEntries(CurrentLogFile));


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
           Pre     => (UsedLogFiles.Length >= 1 and then
                         NumberLogEntries =
                         LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
                         LogFileEntries(CurrentLogFile)),
           Post    => (UsedLogFiles.Length >= 1 and then
                         NumberLogEntries =
                         LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
                         LogFileEntries(CurrentLogFile));


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

   procedure ClearLogEntries (User    : in     AuditTypes.UserTextT)
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
           Pre     => (UsedLogFiles.Length >= 1 and then
                         NumberLogEntries =
                         LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
                         LogFileEntries(CurrentLogFile)),
           Post    => (UsedLogFiles.Length >= 1 and then
                         NumberLogEntries =
                         LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
                         LogFileEntries(CurrentLogFile));


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
