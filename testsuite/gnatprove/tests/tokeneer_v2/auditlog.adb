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
--    Implementation of the AuditLog.
--
------------------------------------------------------------------
with Clock;
with ConfigData;

with AlarmTypes;
use type AlarmTypes.StatusT;

package body AuditLog
  with Refined_State => (State => (AuditAlarm,
                                   CurrentLogFile,
                                   UsedLogFiles,
                                   LogFileEntries,
                                   LogFilesStatus,
                                   NumberLogEntries,
                                   AuditSystemFault),
                         FileState => LogFiles)
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
   LogFiles         : LogFilesT := LogFilesT'(others => File.NullFile);

   CurrentLogFile   : LogFileIndexT;
   LogFilesStatus   : LogFilesStatusT;
   NumberLogEntries : LogEntryCountT;
   UsedLogFiles     : LogFileListT;
   LogFileEntries   : LogFileEntryT;

   AuditAlarm       : AlarmTypes.StatusT;

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

   --  Helper expression function that acts as the precondition of
   --  AddElementToLog, ArchiveLog and ClearLogEntries. It allows us
   --  to refer to types and variables that are declared in the body
   --  and are not visible here and it acts as an invariant.
   function Valid_NumberLogEntries return Boolean is
     (UsedLogFiles.Length >= 1 and then
      NumberLogEntries =
        LogEntryCountT(UsedLogFiles.Length - 1) * MaxLogFileEntries +
        LogFileEntries(CurrentLogFile))
      with Refined_Global => (LogFileEntries,
                              CurrentLogFile,
                              NumberLogEntries,
                              UsedLogFiles);

   ------------------------------------------------------------------
   -- Private Operations
   --
   ------------------------------------------------------------------

   ------------------------------------------------------------------
   -- AgeLessThan
   --
   --    Description:
   --       Compares two date strings.
   --
   ------------------------------------------------------------------
   function AgeLessThan (Left, Right : Clock.TimeTextT) return Boolean is
     (Left < Right);

   ------------------------------------------------------------------
   -- NextListIndex
   --
   --    Description:
   --       Returns the next index, wrapping if necessary.
   --
   --   Implementation Notes:
   --       None.
   --
   ------------------------------------------------------------------
   function NextListIndex(Value : LogFileIndexT) return LogFileIndexT is
     (if Value = LogFileIndexT'Last then
         LogFileIndexT'First
      else
         Value + 1);

   ------------------------------------------------------------------
   -- CheckLogAlarm
   --
   --    Description:
   --       Raises the alarm if the log is too big.
   --
   --   Implementation Notes:
   --       None.
   --
   ------------------------------------------------------------------
   procedure CheckLogAlarm
     with Global  => (Input  => (ConfigData.State,
                                 NumberLogEntries),
                      In_Out => AuditAlarm),
          Depends => (AuditAlarm =>+ (ConfigData.State,
                                      NumberLogEntries))
   is
   begin
      if NumberLogEntries >=
        LogEntryCountT(ConfigData.TheAlarmThresholdEntries) then
         AuditAlarm := AlarmTypes.Alarming;
      end if;
   end CheckLogAlarm;

   ------------------------------------------------------------------
   -- ConvertToAuditDescription
   --
   --    Description:
   --       Converts a string to an audit description.
   --       Truncating if necessary.
   --
   ------------------------------------------------------------------

   function ConvertToAuditDescription
     (Description : String) return AuditTypes.DescriptionT
   is
      LocalDesc : AuditTypes.DescriptionT := AuditTypes.NoDescription;
   begin
      if Description'Length < LocalDesc'Length then
         for I in 0 .. Description'Length - 1 loop
            LocalDesc (LocalDesc'First + I) := Description (Description'First + I);
         end loop;
      else
         for I in 0 .. LocalDesc'Length - 1 loop
            LocalDesc (LocalDesc'First + I) := Description (Description'First + I);
         end loop;
      end if;

      return LocalDesc;
   end ConvertToAuditDescription;

   ------------------------------------------------------------------
   -- GetStartAndEndTimeFromFile
   --
   --    Description:
   --       Extracts the start and end time from a full log file.
   --       As it is full we know how many entries are in the file.
   --
   --   Implementation Notes:
   --       Leaves the file closed.
   --
   ------------------------------------------------------------------
   procedure GetStartAndEndTimeFromFile
     (TheFile     : in out File.T;
      Description :    out AuditTypes.DescriptionT)
     with Global  => (In_Out => AuditSystemFault),
          Depends => ((AuditSystemFault,
                       TheFile)          =>+ TheFile,
                      Description => TheFile)
   is
      OK        : Boolean;
      FirstTime : Clock.TimeTextT;
      LastTime  : Clock.TimeTextT;
      TimeCount : Natural; -- type Natural to match formal parameter
                           -- in call to GetString
      TimeOK    : Boolean := True;

      ------------------------------------------------------------------
      -- ConvertTimesToText
      --
      --    Description:
      --       Returns a Description with Start and End Times of file..
      --
      --   Implementation Notes:
      --       Hidden from SPARK because of use of& in non-Static context.
      --
      ------------------------------------------------------------------
      function ConvertTimesToText return AuditTypes.DescriptionT is
        (if TimeOK then
            ConvertToAuditDescription
              ("From: "& FirstTime & " to: " & LastTime)
         else
            ConvertToAuditDescription
              ("Error obtaining times from file.Best estimate is from: "
               & FirstTime& " to: "& LastTime))
        with Global => (FirstTime, LastTime, TimeOK);

   -------------------------------------------------------------------
   -- begin GetStartAndEndTimeFromFile
   -------------------------------------------------------------------
   begin
      FirstTime := Clock.PrintTime(Clock.ZeroTime);
      LastTime  := Clock.PrintTime(Clock.ZeroTime);

      if File.Exists(TheFile => TheFile) then
         File.OpenRead(TheFile => TheFile,
                       Success => OK);

         AuditSystemFault := AuditSystemFault or not OK;

         if OK then
            -- get the age of the first element
            -- time is the first field on the line
            File.GetString(TheFile => TheFile,
                           Text    => FirstTime,
                           Stop    => TimeCount);

            if TimeCount /= FirstTime'Last then
               -- Time was corrupt
               TimeOK := False;
            end if;

            File.SkipLine(TheFile, MaxLogFileEntries - 1);

            -- get the age of the last element
            File.GetString(TheFile => TheFile,
                           Text    => LastTime,
                           Stop    => TimeCount);

            if TimeCount /= LastTime'Last then
               -- Time was corrupt
               TimeOK := False;
            end if;

         end if;

         File.Close(TheFile => TheFile,
                    Success => OK);

         AuditSystemFault := AuditSystemFault or not OK;

      end if;

      Description := ConvertTimesToText;

   end GetStartAndEndTimeFromFile;

   ------------------------------------------------------------------
   -- UpdateEndTimeFromFile
   --
   --    Description:
   --       Extracts the end time from a full log file.
   --       replaces the end time from the description
   --       with this new value.
   --
   --   Implementation Notes:
   --       Leaves the file closed.
   --
   ------------------------------------------------------------------
   procedure UpdateEndTimeFromFile
     (TheFile     : in out File.T;
      Description : in out AuditTypes.DescriptionT)
     with Global  => (In_Out => AuditSystemFault),
          Depends => ((AuditSystemFault,
                       Description,
                       TheFile) =>+ TheFile)
   is
      OK        : Boolean;
      LastTime  : Clock.TimeTextT;
      TimeCount : Natural; -- type Natural to match formal parameter
                           -- in call to GetString
      TimeOK    : Boolean := True;

      ------------------------------------------------------------------
      -- OverwriteTimeInText
      --
      --    Description:
      --       Returns a Description with Start and End Times of file.
      --
      --   Implementation Notes:
      --       Hidden from SPARK because of use of& in non-Static context.
      --
      ------------------------------------------------------------------
      function OverwriteTimeInText(Description : AuditTypes.DescriptionT)
                                   return AuditTypes.DescriptionT
        with Global  => (LastTime, TimeOK)
      is
         Descr       : AuditTypes.DescriptionT;
         FirstTime   : Clock.TimeTextT;
         Offset      : Positive;
         BothTimesOK : Boolean;
      begin
         BothTimesOK := TimeOK;
         -- get Start Time from Description:
         if Description(Description'First) = 'F' then
            Offset := 6;
         else
            Offset := 56;
            BothTimesOK := False;
         end if;
         FirstTime := Description(Offset + FirstTime'First..
                                  Offset + FirstTime'Last);

         if BothTimesOK then
            Descr := ConvertToAuditDescription
              ("From: "& FirstTime& " to: "& LastTime);
         else
            Descr := ConvertToAuditDescription
              ("Error obtaining times from file.Best estimate is from: "
               & FirstTime & " to: "& LastTime);
         end if;

         return Descr;
      end OverwriteTimeInText;

   -------------------------------------------------------------------
   -- begin UpdateEndTimeFromFile
   -------------------------------------------------------------------
   begin
      LastTime := Clock.PrintTime(Clock.ZeroTime);

      if File.Exists(TheFile => TheFile) then
         File.OpenRead(TheFile => TheFile,
                       Success => OK);

         AuditSystemFault := AuditSystemFault or not OK;

         if OK then
            File.SkipLine(TheFile, MaxLogFileEntries - 1);

            -- get the age of the last element
            -- the time is the first field on the line
            File.GetString(TheFile => TheFile,
                           Text    => LastTime,
                           Stop    => TimeCount);

            if TimeCount /= LastTime'Last then
               -- Time was corrupt
               TimeOK := False;
            end if;

        end if;

        File.Close(TheFile => TheFile,
                   Success => OK);

        AuditSystemFault := AuditSystemFault or not OK;

      end if;

      Description := OverwriteTimeInText(Description);

   end UpdateEndTimeFromFile;

   ------------------------------------------------------------------
   -- DeleteArchiveFile
   --
   --    Description:
   --       Deletes the local copy of the archive file.
   --
   --   Implementation Notes:
   --       Ignore all failures.
   --       This routine has no effect in the SPARK context,
   --       its purpose is to remove a temporary file - not modelled in SPARK.
   ------------------------------------------------------------------
   procedure DeleteArchiveFile
     with SPARK_Mode,
          Depends => null;

   procedure DeleteArchiveFile
     with SPARK_Mode => Off
   is
      Archive : File.T;
      Unused  : Boolean;
   begin
      Archive := File.Construct (TheName => ArchiveFileName);

      File.OpenRead(TheFile => Archive,
                    Success => Unused);
      File.Delete(TheFile => Archive,
                  Success => Unused);

   end DeleteArchiveFile;

   ------------------------------------------------------------------
   -- DeleteLogFile
   --
   --    Description:
   --       Deletes the log file referenced by the index.
   --
   --   Implementation Notes:
   --       None.
   --
   ------------------------------------------------------------------
   procedure DeleteLogFile (Index : LogFileIndexT)
     with Global  => (In_Out => (AuditSystemFault,
                                 LogFileEntries,
                                 LogFiles,
                                 LogFilesStatus)),
          Depends => ((AuditSystemFault,
                       LogFiles)         =>+ (Index,
                                              LogFiles),
                      (LogFileEntries,
                       LogFilesStatus) =>+ Index),
          Post    => (for all I in LogFileIndexT'Range =>
                        (if I /= Index then LogFileEntries (I) = LogFileEntries'Old (I)))
   is
      OK      : Boolean;
      TheFile : File.T;
   begin
      TheFile := LogFiles (Index);

      File.OpenRead(TheFile => TheFile,
                    Success => OK);
      AuditSystemFault := AuditSystemFault and not OK;
      File.Delete(TheFile => TheFile,
                  Success => OK);
      AuditSystemFault := AuditSystemFault and not OK;

      LogFiles(Index) := TheFile;

      LogFilesStatus (Index) := Free;
      LogFileEntries (Index) := 0;

   end DeleteLogFile;

   ------------------------------------------------------------------
   -- AddElementToFile
   --
   --    Description:
   --       Puts an entry in the log file.
   --
   --   Implementation Notes:
   --       Leaves the file closed.
   --
   ------------------------------------------------------------------
   procedure AddElementToFile (
                TheFile     : in out File.T;
                ElementID   : in     AuditTypes.ElementT;
                Severity    : in     AuditTypes.SeverityT;
                User        : in     AuditTypes.UserTextT;
                Description : in     AuditTypes.DescriptionT)
     with Global  => (Input  => Clock.Now,
                      In_Out => AuditSystemFault),
          Depends => ((AuditSystemFault,
                       TheFile)          =>+ (Clock.Now,
                                              Description,
                                              ElementID,
                                              Severity,
                                              TheFile,
                                              User))
   is
      OK  : Boolean;
      Now : Clock.TimeT;

      ------------------------------------------------------------------
      -- NameOfType
      --
      --   Description:
      --      Returns a string containing the name of the element type.
      --
      --   Implementation Notes:
      --       Hidden as it uses 'IMAGE and slicing.
      --
      ------------------------------------------------------------------
      function NameOfType (E : AuditTypes.ElementT) return ElementTextT
      is
         ElementText : ElementTextT := NoElement;
      begin
         ElementText(1..AuditTypes.ElementT'Image(ElementID)'Last) :=
           AuditTypes.ElementT'Image(ElementID);

         return ElementText;
      end NameOfType;

   -------------------------------------------------------------------
   -- begin AddElementToFile
   -------------------------------------------------------------------
   begin
      Now := Clock.GetNow;

      File.OpenAppend (TheFile, OK);
      if not OK then
         -- if can't open then create it and it is empty
         File.Create(TheFile => TheFile,
                     Success => OK);
      end if;

      if OK then
         -- Write Time
         File.PutString(TheFile => TheFile,
                        Text    => Clock.PrintTime(Now),
                        Stop    => 0);

         File.PutString(TheFile => TheFile,
                        Text    => ", ",
                        Stop    => 0);

         -- Write Severity
         File.PutInteger(TheFile => TheFile,
                         Item   => AuditTypes.SeverityT'Pos(Severity)+ 1,
                         Width  => 1);

         File.PutString(TheFile => TheFile,
                        Text    => ", ",
                        Stop    => 0);

         -- Write type
         File.PutInteger(TheFile => TheFile,
                         Item    => AuditTypes.ElementT'Pos(ElementID),
                         Width   => 2);

         File.PutString(TheFile => TheFile,
                        Text    => ", ",
                        Stop    => 0);

         File.PutString(TheFile => TheFile,
                        Text   => NameOfType (ElementID),
                        Stop => 0);

         File.PutString(TheFile => TheFile,
                        Text    => ", ",
                        Stop    => 0);

         -- Write user
         File.PutString(TheFile => TheFile,
                        Text    => User,
                        Stop    => 0);

         File.PutString(TheFile => TheFile,
                        Text    => ", ",
                        Stop    => 0);

         -- Write description
         File.PutString(TheFile => TheFile,
                        Text    => Description,
                        Stop    => 0);

         File.NewLine(TheFile => TheFile,
                      Spacing => 1);

      else
         AuditSystemFault := True;
      end if;

      File.Close (TheFile => TheFile,
                  Success => OK);

      if not OK then
         AuditSystemFault := True;
      end if;
   end AddElementToFile;

   ------------------------------------------------------------------
   -- AddElementToLogFile
   --
   --    Description:
   --       Puts the entry in the log file,
   --             either the current file or the next file..
   --
   --   Implementation Notes:
   --       Leaves the file closed.
   --
   ------------------------------------------------------------------
   procedure AddElementToLogFile
     (ElementID   : in     AuditTypes.ElementT;
      Severity    : in     AuditTypes.SeverityT;
      User        : in     AuditTypes.UserTextT;
      Description : in     AuditTypes.DescriptionT)
     with Global  => (Input  => Clock.Now,
                      In_Out => (AuditSystemFault,
                                 CurrentLogFile,
                                 LogFileEntries,
                                 LogFiles,
                                 LogFilesStatus,
                                 NumberLogEntries,
                                 UsedLogFiles)),
          Depends => ((AuditSystemFault,
                       LogFiles)         =>+ (Clock.Now,
                                              CurrentLogFile,
                                              Description,
                                              ElementID,
                                              LogFileEntries,
                                              LogFiles,
                                              LogFilesStatus,
                                              Severity,
                                              User),
                      (CurrentLogFile,
                       LogFileEntries,
                       LogFilesStatus,
                       UsedLogFiles)   =>+ (CurrentLogFile,
                                            LogFileEntries,
                                            LogFilesStatus),
                      NumberLogEntries =>+ null),
          Pre     => NumberLogEntries < MaxLogEntries and then
                     (LogFileEntries(CurrentLogFile) < MaxLogFileEntries or else
                       UsedLogFiles.Length < LogFileCountT'Last) and then
                     NumberLogEntries =
                       LogEntryCountT(UsedLogFiles.Length - 1) * MaxLogFileEntries +
                       LogFileEntries(CurrentLogFile),
          Post    => NumberLogEntries =
                       LogEntryCountT(UsedLogFiles.Length - 1) * MaxLogFileEntries +
                       LogFileEntries(CurrentLogFile) and then
                     NumberLogEntries = NumberLogEntries'Old + 1 and then
                     ((LogFileEntries(CurrentLogFile)'Old = MaxLogFileEntries) <=
                       (LogFileEntries(CurrentLogFile) = 1 and then
                        UsedLogFiles.Length = UsedLogFiles'Old.Length + 1)) and then
                     ((LogFileEntries(CurrentLogFile)'Old < MaxLogFileEntries) <=
                       (LogFileEntries(CurrentLogFile) =
                          LogFileEntries(CurrentLogFile)'Old + 1 and then
                          UsedLogFiles.Length = UsedLogFiles'Old.Length))
   is
      ------------------------------------------------------------------
      -- AddElementToCurrentFile
      --
      --    Description:
      --       Adds an element to the current log file.
      --
      --   Implementation Notes:
      --       Leaves the file closed.
      --
      ------------------------------------------------------------------
      procedure AddElementToCurrentFile
        (ElementID   : in     AuditTypes.ElementT;
         Severity    : in     AuditTypes.SeverityT;
         User        : in     AuditTypes.UserTextT;
         Description : in     AuditTypes.DescriptionT)
        with Global  => (Input  => (Clock.Now,
                                    CurrentLogFile),
                         In_Out => (AuditSystemFault,
                                    LogFileEntries,
                                    LogFiles)),
             Depends => ((AuditSystemFault,
                          LogFiles)         =>+ (Clock.Now,
                                                 CurrentLogFile,
                                                 Description,
                                                 ElementID,
                                                 LogFiles,
                                                 Severity,
                                                 User),
                         LogFileEntries =>+ CurrentLogFile),
             Pre     => LogFileEntries(CurrentLogFile) < MaxLogFileEntries,
             Post    => LogFileEntries(CurrentLogFile) = LogFileEntries'Old(CurrentLogFile) + 1
      is
         TheFile : File.T;
      begin
         TheFile := LogFiles (CurrentLogFile);
         AddElementToFile
           (TheFile     => TheFile,
            ElementID   => ElementID,
            Severity    => Severity,
            User        => User,
            Description => Description);
         LogFiles (CurrentLogFile) := TheFile;

         LogFileEntries(CurrentLogFile) := LogFileEntries(CurrentLogFile) + 1;
      end AddElementToCurrentFile;

      ------------------------------------------------------------------
      -- AddElementToNextFile
      --
      --    Description:
      --       Adds an element to the next empty log file.
      --
      --   Implementation Notes:
      --      Leaves file closed.
      --
      ------------------------------------------------------------------
      procedure AddElementToNextFile
        (ElementID   : in     AuditTypes.ElementT;
         Severity    : in     AuditTypes.SeverityT;
         User        : in     AuditTypes.UserTextT;
         Description : in     AuditTypes.DescriptionT)
        with Global  => (Input  => Clock.Now,
                         In_Out => (AuditSystemFault,
                                    CurrentLogFile,
                                    LogFileEntries,
                                    LogFiles,
                                    LogFilesStatus,
                                    UsedLogFiles)),
             Depends => ((AuditSystemFault,
                          LogFiles)         =>+ (Clock.Now,
                                                 CurrentLogFile,
                                                 Description,
                                                 ElementID,
                                                 LogFiles,
                                                 LogFilesStatus,
                                                 Severity,
                                                 User),
                         (CurrentLogFile,
                          LogFileEntries,
                          LogFilesStatus,
                          UsedLogFiles)   =>+ (CurrentLogFile,
                                               LogFilesStatus)),
             Pre     => UsedLogFiles.Length < LogFileCountT'Last,
             Post    => UsedLogFiles.Length = UsedLogFiles.Length'Old + 1 and then
                          LogFileEntries(CurrentLogFile) = 1
      is
         TheFile : File.T;

         procedure SetCurrentFileToNextFreeFile
           with Global  => (Input  => LogFilesStatus,
                            In_Out => CurrentLogFile),
                Depends => (CurrentLogFile =>+ LogFilesStatus)
         is
         begin
            for I in LogFileIndexT loop
               if LogFilesStatus(I) = Free then
                  CurrentLogFile := I;
                  exit;
               end if;
            end loop;
         end SetCurrentFileToNextFreeFile;

      -------------------------------------------------
      -- AddElementToNextFile
      -------------------------------------------------
      begin
         SetCurrentFileToNextFreeFile;

         LogFilesStatus(CurrentLogFile) := Used;

         -- add currentLogFile' to end of list of UsedLogFiles.
         UsedLogFiles.Length := UsedLogFiles.Length + 1;
         UsedLogFiles.LastI := NextListIndex(UsedLogFiles.LastI);
         UsedLogFiles.List(UsedLogFiles.LastI) := CurrentLogFile;

         TheFile := LogFiles (CurrentLogFile);
         AddElementToFile
           (TheFile     => TheFile,
            ElementID   => ElementID,
            Severity    => Severity,
            User        => User,
            Description => Description);
         LogFiles (CurrentLogFile) := TheFile;

         LogFileEntries(CurrentLogFile) := 1;

      end AddElementToNextFile;

   -------------------------------------------------
   -- AddElementToLogFile
   ------------------------------------------------
   begin
      if LogFileEntries(CurrentLogFile) < MaxLogFileEntries then

         AddElementToCurrentFile
           (ElementID   => ElementID,
            Severity    => Severity,
            User        => User,
            Description => Description);

      else

         AddElementToNextFile
           (ElementID   => ElementID,
            Severity    => Severity,
            User        => User,
            Description => Description);
      end if;

      NumberLogEntries := NumberLogEntries + 1;

   end AddElementToLogFile;

   ------------------------------------------------------------------
   -- TruncateLog
   --
   --    Description:
   --       Truncates the log.
   --
   --   Implementation Notes:
   --       Leaves all files closed.
   --
   ------------------------------------------------------------------
   procedure TruncateLog(Description : out AuditTypes.DescriptionT)
     with Global  => (Output   => AuditAlarm,
                      In_Out   => (AuditSystemFault,
                                   LogFileEntries,
                                   LogFiles,
                                   LogFilesStatus,
                                   NumberLogEntries,
                                   UsedLogFiles),
                      Proof_In => CurrentLogFile),
          Depends => (AuditAlarm => null,
                      (AuditSystemFault,
                       LogFiles)         =>+ (LogFiles,
                                              UsedLogFiles),
                      Description => (LogFiles,
                                      UsedLogFiles),
                      (LogFileEntries,
                       LogFilesStatus,
                       UsedLogFiles)   =>+ UsedLogFiles,
                      NumberLogEntries =>+ null),
          Pre     => UsedLogFiles.Length >= 1 and then
                     UsedLogFiles.Length = LogFileCountT'Last and then
                     NumberLogEntries =
                       LogEntryCountT(UsedLogFiles.Length) * MaxLogFileEntries,
          Post    => UsedLogFiles.Length >= 1 and then
                     LogFileEntries (CurrentLogFile) = LogFileEntries'Old (CurrentLogFile'Old) and then
                     UsedLogFiles.Length = LogFileCountT'Last - 1 and then
                     NumberLogEntries =
                       LogEntryCountT(UsedLogFiles.Length) * MaxLogFileEntries
   is
      TheFile : File.T;
      Head    : LogFileIndexT;
   begin
      Head := UsedLogFiles.List(UsedLogFiles.Head);

      -- Make description
      TheFile := LogFiles (Head);
      GetStartAndEndTimeFromFile
        (TheFile     => TheFile,
         Description => Description);
      LogFiles (Head) := TheFile;

      pragma Assume (Head /= CurrentLogFile);

      -- Empty the file.
      DeleteLogFile (Head);

      -- remove the head of the usedLogFiles
      UsedLogFiles.Head := NextListIndex (UsedLogFiles.Head);
      UsedLogFiles.Length := UsedLogFiles.Length - 1;

      NumberLogEntries := NumberLogEntries - MaxLogFileEntries;

      AuditAlarm := AlarmTypes.Alarming;
   end TruncateLog;

   ------------------------------------------------------------------
   -- AddElementToLogFileWithTruncateChecks
   --
   --    Description:
   --       Checks whether the log is full - truncates if it is.
   --       If Truncation happened, put truncation entry in
   --           the log file.
   --       Finally puts the entry in the log file,
   --             either the current file or the next file.
   --
   --   Implementation Notes:
   --       Leaves the file closed.
   --
   ------------------------------------------------------------------
   procedure AddElementToLogFileWithTruncateChecks
     (ElementID   : in     AuditTypes.ElementT;
      Severity    : in     AuditTypes.SeverityT;
      User        : in     AuditTypes.UserTextT;
      Description : in     AuditTypes.DescriptionT)
     with Global  => (Input  => Clock.Now,
                      In_Out => (AuditAlarm,
                                 AuditSystemFault,
                                 CurrentLogFile,
                                 LogFileEntries,
                                 LogFiles,
                                 LogFilesStatus,
                                 NumberLogEntries,
                                 UsedLogFiles)),
          Depends => ((AuditAlarm,
                       LogFilesStatus,
                       NumberLogEntries) =>+ (CurrentLogFile,
                                              LogFileEntries,
                                              UsedLogFiles),
                      (AuditSystemFault, LogFiles) =>+ (Clock.Now,
                                                        CurrentLogFile,
                                                        Description,
                                                        ElementID,
                                                        LogFileEntries,
                                                        LogFiles,
                                                        LogFilesStatus,
                                                        Severity,
                                                        UsedLogFiles,
                                                        User),
                      (CurrentLogFile,
                       LogFileEntries,
                       UsedLogFiles)   => (CurrentLogFile,
                                           LogFileEntries,
                                           LogFilesStatus,
                                           UsedLogFiles)),
          Pre  => UsedLogFiles.Length >= 1 and then
                  NumberLogEntries =
                    LogEntryCountT(UsedLogFiles.Length - 1) * MaxLogFileEntries +
                    LogFileEntries(CurrentLogFile),
          Post => UsedLogFiles.Length >= 1 and then
                  NumberLogEntries =
                    LogEntryCountT(UsedLogFiles.Length - 1) * MaxLogFileEntries +
                    LogFileEntries(CurrentLogFile)
   is
      TruncateDescription : AuditTypes.DescriptionT;
   begin
      if LogFileEntries(CurrentLogFile) = MaxLogFileEntries
        and UsedLogFiles.Length = LogFileCountT'Last
      then

         TruncateLog(Description => TruncateDescription);

         AddElementToLogFile
           (ElementID   => AuditTypes.TruncateLog,
            Severity    => AuditTypes.Critical,
            User        => AuditTypes.NoUser,
            Description => TruncateDescription);

      end if;

      AddElementToLogFile
        (ElementID   => ElementID,
         Severity    => Severity,
         User        => User,
         Description => Description);

   end AddElementToLogFileWithTruncateChecks;

   ------------------------------------------------------------------
   -- Public Operations
   --
   ------------------------------------------------------------------

   ------------------------------------------------------------------
   -- Init
   --
   --    Implementation Notes:
   --       All files are either free or used.
   --
   ------------------------------------------------------------------
   procedure Init
     with Refined_Global  => (Input  => ConfigData.State,
                              Output => (AuditAlarm,
                                         AuditSystemFault,
                                         CurrentLogFile,
                                         LogFileEntries,
                                         LogFilesStatus,
                                         NumberLogEntries,
                                         UsedLogFiles),
                              In_Out => LogFiles),
          Refined_Depends => (AuditAlarm => (ConfigData.State, LogFiles),
                              (AuditSystemFault,
                               CurrentLogFile,
                               LogFileEntries,
                               LogFiles,
                               LogFilesStatus,
                               NumberLogEntries,
                               UsedLogFiles) => LogFiles),
          Refined_Post    => UsedLogFiles.Length >= 1 and then
                             NumberLogEntries =
                               LogEntryCountT(UsedLogFiles.Length - 1) * MaxLogFileEntries +
                               LogFileEntries(CurrentLogFile)
   is
     type FileAgeT is array (LogFileIndexT) of Clock.TimeTextT;
     FileAges : FileAgeT;
     OK       : Boolean;

     ------------------------------------------------------------------
     -- SetFileDetails
     --
     --    Description:
     --       Sets much of the log file state.
     --       In particular determines the logFileStatus, logFileEntries
     --       and creates a handle to each of the logFiles.
     --       It also obtains the oldest element in each log file as a
     --       prelude to creating the sorted list of usedLogFiles.
     --
     --   Implementation Notes:
     --      None
     --
     ------------------------------------------------------------------
     procedure SetFileDetails
       with Global  => (Output => (FileAges,
                                   LogFileEntries,
                                   LogFilesStatus),
                        In_Out => (AuditSystemFault,
                                   LogFiles)),
            Depends => ((AuditSystemFault,
                         LogFiles)         =>+ LogFiles,
                        (FileAges,
                         LogFileEntries,
                         LogFilesStatus) => LogFiles)
     is
        FileH         : File.T;
        Status        : FileStatusT;
        NumberEntries : FileEntryCountT;
        FirstTime     : Clock.TimeTextT;

        ------------------------------------------------------------------
        -- GetFileDetails
        --
        --    Description:
        --       Gets all the necessary information from a single file.
        --
        --   Implementation Notes:
        --      None.
        --
        ------------------------------------------------------------------
        procedure GetFileDetails (I : in LogFileIndexT)
          with Global  => (Input  => LogFiles,
                           Output => (FileH,
                                      FirstTime,
                                      NumberEntries,
                                      Status),
                           In_Out => AuditSystemFault),
               Depends => (AuditSystemFault =>+ (I,
                                                 LogFiles),
                           (FileH,
                            FirstTime,
                            NumberEntries,
                            Status)        => (I,
                                               LogFiles))
        is
           OK        : Boolean;
           TimeOK    : Boolean := True;
           TimeCount : Natural;
        begin
           -- Try to open the file
           NumberEntries := 0;
           FirstTime := Clock.PrintTime(Clock.ZeroTime);
           FileH := LogFiles(I);
           File.SetName (TheName => LogFileNames(I),
                         TheFile => FileH);

           if File.Exists(TheFile => FileH) then
              File.OpenRead(TheFile => FileH,
                            Success => OK);
              if OK then
                 -- if can open then see if it is empty
                 if File.EndOfFile(FileH) then
                    Status := Free;
                 else
                    Status := Used;
                    -- get the age of the first element
                    File.GetString(TheFile => FileH,
                                   Text    => FirstTime,
                                   Stop    => TimeCount);
                    if TimeCount /= FirstTime'Last then
                       -- Time was corrupt
                       TimeOK := False;
                    end if;
                    -- See how full it is
                    while not File.EndOfFile(FileH) loop
                       pragma Assume (NumberEntries < MaxLogFileEntries);
                       File.SkipLine(FileH, 1);
                       NumberEntries := NumberEntries + 1;
                       exit when NumberEntries = MaxLogFileEntries;
                    end loop;
                 end if;

              else -- File exists but can't be opened.
                 Status := Used;
                 AuditSystemFault := True;
              end if;

              File.Close(TheFile => FileH,
                         Success => OK);
              if not OK or not TimeOK then
                 AuditSystemFault := True;
              end if;

           else -- File doesn't exist so it is free
              -- (will be created when need to write to it).

              Status := Free;

           end if;

        end GetFileDetails;

     ------------------------------------------------------------------
     -- begin SetFileDetails
     ------------------------------------------------------------------
     begin

        --# accept F, 23, LogFilesStatus, "Array initialization is total in loop"& F, 23, LogFileEntries, "Array initialization is total in loop"& F, 23, FileAges, "Array initialization is total in loop";
        for I in LogFileIndexT loop
           GetFileDetails(I);
           LogFilesStatus(I) := Status;
           LogFiles(I)       := FileH;
           FileAges(I)       := FirstTime;
           LogFileEntries(I) := NumberEntries;
        end loop;

        --# accept F, 602, LogFilesStatus, LogFilesStatus, "Array initialization is total in loop"& F, 602, LogFileEntries, LogFileEntries, "Array initialization is total in loop"& F, 602, FileAges, FileAges, "Array initialization is total in loop";
     end SetFileDetails;

   ------------------------------------------------------------------
   -- begin Init
   ------------------------------------------------------------------
   begin
      File.CreateDirectory(DirName => LogDirectory,
                           Success => OK);

      AuditSystemFault := not OK;

      SetFileDetails;

      -- Now put the used files in order in the list.

      UsedLogFiles := EmptyList;
      for I in LogFileIndexT loop
         if LogFilesStatus(I) = Used then
            if UsedLogFiles.Length = 0 then
               -- easy case list currently empty
               UsedLogFiles.Head := LogFileIndexT'First;
               UsedLogFiles.LastI := LogFileIndexT'First;
               UsedLogFiles.Length := 1;
               UsedLogFiles.List(UsedLogFiles.Head) := I;
            else
               for J in LogFileIndexT range 1..UsedLogFiles.LastI loop
                  if AgeLessThan(FileAges(I), FileAges(UsedLogFiles.List(J))) then
                     -- this is where the new entry goes.
                     -- move all other entries up the list to make room
                     UsedLogFiles.LastI  := UsedLogFiles.LastI + 1;
                     UsedLogFiles.Length := UsedLogFiles.Length + 1;
                     for K in reverse LogFileIndexT
                       range J + 1..UsedLogFiles.LastI
                     loop
                        UsedLogFiles.List(K) := UsedLogFiles.List(K - 1);
                     end loop;
                     UsedLogFiles.List(J) := I;
                     exit;
                  end if;
                  if J = UsedLogFiles.LastI then
                     -- entry goes at the end
                     UsedLogFiles.LastI  := UsedLogFiles.LastI + 1;
                     UsedLogFiles.Length := UsedLogFiles.Length + 1;
                     UsedLogFiles.List(UsedLogFiles.LastI) := I;
                     exit;
                  end if;
               end loop;
            end if;
         end if;
      end loop;

      if UsedLogFiles.Length = 0 then
         CurrentLogFile := LogFileIndexT'First;
         -- The current file is the first used file.
         UsedLogFiles.Head := LogFileIndexT'First;
         UsedLogFiles.LastI := LogFileIndexT'First;
         UsedLogFiles.Length := 1;
         UsedLogFiles.List(UsedLogFiles.Head) := CurrentLogFile;
         LogFilesStatus(CurrentLogFile) := Used;
      else
         CurrentLogFile := UsedLogFiles.List(UsedLogFiles.LastI);
      end if;

      NumberLogEntries := LogEntryCountT(UsedLogFiles.Length - 1) * MaxLogFileEntries
        + LogFileEntries(CurrentLogFile);

      AuditAlarm := AlarmTypes.Silent;
      CheckLogAlarm;

   end Init;

   ------------------------------------------------------------------
   -- AddElementToLog
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure AddElementToLog (
                ElementID   : in     AuditTypes.ElementT;
                Severity    : in     AuditTypes.SeverityT;
                User        : in     AuditTypes.UserTextT;
                Description : in     String)
     with Refined_Global  => (Input  => (Clock.Now,
                                         ConfigData.State),
                              In_Out => (AuditAlarm,
                                         AuditSystemFault,
                                         CurrentLogFile,
                                         LogFileEntries,
                                         LogFiles,
                                         LogFilesStatus,
                                         NumberLogEntries,
                                         UsedLogFiles)),
          Refined_Depends => ((AuditAlarm,
                               CurrentLogFile,
                               LogFileEntries,
                               LogFilesStatus,
                               NumberLogEntries,
                               UsedLogFiles)     => (AuditAlarm,
                                                     ConfigData.State,
                                                     CurrentLogFile,
                                                     LogFileEntries,
                                                     LogFilesStatus,
                                                     NumberLogEntries,
                                                     UsedLogFiles),
                              (AuditSystemFault,
                               LogFiles)         =>+ (AuditAlarm,
                                                      Clock.Now,
                                                      ConfigData.State,
                                                      CurrentLogFile,
                                                      Description,
                                                      ElementID,
                                                      LogFileEntries,
                                                      LogFiles,
                                                      LogFilesStatus,
                                                      NumberLogEntries,
                                                      Severity,
                                                      UsedLogFiles,
                                                      User)),
          --  Refined_Pre     => (UsedLogFiles.Length >= 1 and then
          --                        NumberLogEntries =
          --                        LogEntryCountT(UsedLogFiles.Length - 1) * MaxLogFileEntries +
          --                        LogFileEntries(CurrentLogFile)),
          --  This has been substituted by a call to Valid_NumberLogEntries
          --  at the specs
          Refined_Post    => UsedLogFiles.Length >= 1 and then
                             NumberLogEntries =
                               LogEntryCountT(UsedLogFiles.Length - 1) * MaxLogFileEntries +
                               LogFileEntries(CurrentLogFile)
   is
      OldAlarm : AlarmTypes.StatusT;
   begin
      OldAlarm := AuditAlarm;

      AddElementToLogFileWithTruncateChecks
        (ElementID   => ElementID,
         Severity    => Severity,
         User        => User,
         Description => ConvertToAuditDescription (Description));

      CheckLogAlarm;

      if OldAlarm /= AuditAlarm then
         -- This will always raise alarms not clear them
         AddElementToLogFileWithTruncateChecks
           (ElementID   => AuditTypes.AuditAlarmRaised,
            Severity    => AuditTypes.Warning,
            User        => AuditTypes.NoUser,
            Description => AuditTypes.NoDescription);
      end if;
   end AddElementToLog;

   ------------------------------------------------------------------
   -- ArchiveLog
   --
   --   Implementation Notes:
   --      None.
   ------------------------------------------------------------------
   procedure ArchiveLog (User    : in     AuditTypes.UserTextT;
                         Archive :    out File.T)
     with Refined_Global  => (Input  => (Clock.Now,
                                         ConfigData.State),
                              In_Out => (AuditAlarm,
                                         AuditSystemFault,
                                         CurrentLogFile,
                                         LogFileEntries,
                                         LogFiles,
                                         LogFilesStatus,
                                         NumberLogEntries,
                                         UsedLogFiles)),
          Refined_Depends => (Archive => (LogFileEntries,
                                          LogFiles,
                                          UsedLogFiles),
                              (AuditAlarm,
                               CurrentLogFile,
                               LogFileEntries,
                               LogFilesStatus,
                               NumberLogEntries,
                               UsedLogFiles)     => (AuditAlarm,
                                                     ConfigData.State,
                                                     CurrentLogFile,
                                                     LogFileEntries,
                                                     LogFiles,
                                                     LogFilesStatus,
                                                     NumberLogEntries,
                                                     UsedLogFiles),
                              (AuditSystemFault,
                               LogFiles)         =>+ (AuditAlarm,
                                                      Clock.Now,
                                                      ConfigData.State,
                                                      CurrentLogFile,
                                                      LogFileEntries,
                                                      LogFiles,
                                                      LogFilesStatus,
                                                      NumberLogEntries,
                                                      UsedLogFiles,
                                                      User)),
          --  Refined_Pre     => (UsedLogFiles.Length >= 1 and then
          --                        NumberLogEntries =
          --                        LogEntryCountT(UsedLogFiles.Length - 1) * MaxLogFileEntries +
          --                        LogFileEntries(CurrentLogFile)),
          --  This has been substituted by a call to Valid_NumberLogEntries
          --  at the specs
          Refined_Post    => UsedLogFiles.Length >= 1 and then
                             NumberLogEntries =
                               LogEntryCountT(UsedLogFiles.Length - 1) * MaxLogFileEntries +
                               LogFileEntries(CurrentLogFile)
   is
      Description         : AuditTypes.DescriptionT;
      TheFile             : File.T;
      OK                  : Boolean;
      ArchiveFault        : Boolean := False;
      ArchivedFileCount   : LogFileCountT;
      FileIndex           : LogFileIndexT;
      FileIndexInUsedList : LogFileIndexT;
   begin
      Archive := File.Construct (TheName => ArchiveFileName);

      Description := ConvertToAuditDescription("Nothing archived");

      if UsedLogFiles.Length = 0 or
        (UsedLogFiles.Length = 1 and
           LogFileEntries(UsedLogFiles.List(UsedLogFiles.Head))
           < MaxLogFileEntries) then
         -- Make an empty file to return

         File.OpenWrite(TheFile => Archive,
                         Success => OK);

         --# accept F, 22, "Invariant expression expected and OK here";
         if not OK then
            File.Create(TheFile => Archive,
                        Success => OK);
         end if;
         --# end accept;

         ArchiveFault := not OK;

         File.Close(TheFile => Archive,
                    Success => OK);

         ArchiveFault := ArchiveFault or not OK;

      else
         ArchivedFileCount := 0;
         FileIndexInUsedList := UsedLogFiles.Head;

         while ArchivedFileCount < MaxNumberArchivableFiles
            and ArchivedFileCount < UsedLogFiles.Length loop
            pragma Loop_Invariant
              (NumberLogEntries =
                 LogEntryCountT(UsedLogFiles.Length - 1) * MaxLogFileEntries +
                 LogFileEntries(CurrentLogFile));

            FileIndex := UsedLogFiles.List(FileIndexInUsedList);
            exit when LogFileEntries(FileIndex) < MaxLogFileEntries;

            TheFile := LogFiles (FileIndex);

            File.Copy (FileA   => TheFile,
                       FileB   => Archive,
                       Success => OK);

            ArchiveFault := not OK;

            exit when ArchiveFault; -- if the copy didn't work don't continue
                                    -- file is not marked as archived.

            LogFilesStatus(FileIndex) := Archived;

            if ArchivedFileCount = 0 then
               GetStartAndEndTimeFromFile
                 (TheFile     => TheFile,
                  Description => Description);
            else
               UpdateEndTimeFromFile
                 (TheFile     => TheFile,
                  Description => Description);
            end if;

            LogFiles (FileIndex) := TheFile;
            ArchivedFileCount := ArchivedFileCount + 1;
            FileIndexInUsedList := NextListIndex (FileIndexInUsedList);

         end loop;

      end if;

      if ArchiveFault then
         AddElementToLog
           (ElementID   => AuditTypes.SystemFault,
            Severity    => AuditTypes.Warning,
            User        => AuditTypes.NoUser,
            Description => "Fault creating archive");
      end if;

      -- As we always add at least one element to the log the CurrentLogFile cannot
      -- be archived.

      AddElementToLog (
                ElementID   => AuditTypes.ArchiveLog,
                Severity    => AuditTypes.Information,
                User        => User,
                Description => Description);

   end ArchiveLog;

   ------------------------------------------------------------------
   -- ClearLogEntries
   --
   --   Implementation Notes:
   --      The archived files will be at the head of the
   --      list of used files so search the list of used files.
   ------------------------------------------------------------------
   procedure ClearLogEntries (User : in     AuditTypes.UserTextT)
     with Refined_Global  => (Input  => (Clock.Now,
                                         ConfigData.State),
                              In_Out => (AuditAlarm,
                                         AuditSystemFault,
                                         CurrentLogFile,
                                         LogFileEntries,
                                         LogFiles,
                                         LogFilesStatus,
                                         NumberLogEntries,
                                         UsedLogFiles)),
          Refined_Depends => ((AuditAlarm,
                               CurrentLogFile,
                               LogFileEntries,
                               LogFilesStatus,
                               NumberLogEntries,
                               UsedLogFiles)     => (AuditAlarm,
                                                     ConfigData.State,
                                                     CurrentLogFile,
                                                     LogFileEntries,
                                                     LogFilesStatus,
                                                     NumberLogEntries,
                                                     UsedLogFiles),
                              (AuditSystemFault,
                               LogFiles)         =>+ (AuditAlarm,
                                                      Clock.Now,
                                                      ConfigData.State,
                                                      CurrentLogFile,
                                                      LogFileEntries,
                                                      LogFiles,
                                                      LogFilesStatus,
                                                      NumberLogEntries,
                                                      UsedLogFiles,
                                                      User)),
          --  Refined_Pre     => (UsedLogFiles.Length >= 1 and then
          --                        NumberLogEntries =
          --                        LogEntryCountT(UsedLogFiles.Length - 1) * MaxLogFileEntries +
          --                        LogFileEntries(CurrentLogFile)),
          --  This has been substituted by a call to Valid_NumberLogEntries
          --  at the specs
          Refined_Post    => UsedLogFiles.Length >= 1 and then
                             NumberLogEntries =
                               LogEntryCountT(UsedLogFiles.Length - 1) * MaxLogFileEntries +
                               LogFileEntries(CurrentLogFile)
   is
      OldAlarm : AlarmTypes.StatusT;
   begin
      -- Note the CurrentLogFile cannot be Archived.

      while UsedLogFiles.Length > 1 loop
         pragma Loop_Invariant
           (UsedLogFiles.Length > 1 and then
            NumberLogEntries =
              LogEntryCountT(UsedLogFiles.Length - 1) * MaxLogFileEntries +
              LogFileEntries(CurrentLogFile));
         exit when LogFilesStatus(UsedLogFiles.List(UsedLogFiles.Head))
           /= Archived;
         pragma Loop_Invariant
           (UsedLogFiles.Length > 1 and then
            LogFilesStatus(UsedLogFiles.List(UsedLogFiles.Head))
              = Archived and then
            NumberLogEntries =
              LogEntryCountT(UsedLogFiles.Length - 1) * MaxLogFileEntries +
              LogFileEntries(CurrentLogFile));

         pragma Assume (UsedLogFiles.List(UsedLogFiles.Head) /= CurrentLogFile);

         -- Empty the archived file.
         DeleteLogFile (UsedLogFiles.List(UsedLogFiles.Head));

         UsedLogFiles.Length := UsedLogFiles.Length - 1;
         UsedLogFiles.Head := NextListIndex (UsedLogFiles.Head);

         NumberLogEntries := NumberLogEntries - MaxLogFileEntries;

      end loop;

      OldAlarm := AuditAlarm;

      AuditAlarm := AlarmTypes.Silent;
      CheckLogAlarm;

      if OldAlarm /= AuditAlarm then
         -- Archiving will always clear alarms not raise them.
         -- Note that adding this entry could result in the alarm
         -- being raised again (this will be handled by AddElementToLog).
         AddElementToLog
           (ElementID   => AuditTypes.AuditAlarmSilenced,
            Severity    => AuditTypes.Information,
            User        => AuditTypes.NoUser,
            Description => AuditTypes.NoDescription);

      end if;

      AddElementToLog
        (ElementID   => AuditTypes.ArchiveComplete,
         Severity    => AuditTypes.Information,
         User        => User,
         Description => AuditTypes.NoDescription);

      pragma Warnings (Off, "statement has no effect [ineffective]");
      DeleteArchiveFile;
      pragma Warnings (On, "statement has no effect [ineffective]");

   end ClearLogEntries;

   ------------------------------------------------------------------
   -- CancelArchive
   --
   --   Implementation Notes:
   --      This does not add log entries.
   ------------------------------------------------------------------
   procedure CancelArchive
     with Refined_Global  => (In_Out => LogFilesStatus),
          Refined_Depends => (LogFilesStatus =>+ null)
   is
   begin
      for I in LogFileIndexT loop
         if LogFilesStatus(I) = Archived then
            LogFilesStatus(I) := Used;
         end if;
      end loop;

      pragma Warnings (Off, "statement has no effect [ineffective]");
      DeleteArchiveFile;
      pragma Warnings (On, "statement has no effect [ineffective]");

   end CancelArchive;

   ------------------------------------------------------------------
   -- TheAuditAlarm
   --
   --   Implementation Notes:
   --      None
   ------------------------------------------------------------------
   function TheAuditAlarm return AlarmTypes.StatusT is (AuditAlarm)
     with Refined_Global  => AuditAlarm;

   ------------------------------------------------------------------
   -- SystemFaultOccurred
   --
   --   Implementation Notes:
   --      None
   ------------------------------------------------------------------
   function SystemFaultOccurred return Boolean is (AuditSystemFault)
     with Refined_Global  => AuditSystemFault;

end AuditLog;
