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
  with Refined_State => (State     => (AuditAlarm,
                                       LogFileState,
                                       LogFilesStatus,
                                       AuditSystemFault),
                         FileState => LogFiles)
is
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
     (if Value = LogFileIndexT'Last then LogFileIndexT'First
      else Value + 1);

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
   procedure CheckLogAlarm (LogFileState : LogFileStateT)
     with Global  => (Input  => ConfigData.State,
                      In_Out => AuditAlarm),
          Depends => (AuditAlarm =>+ (ConfigData.State,
                                      LogFileState))
   is
   begin
      if LogFileState.NumberLogEntries >=
        LogEntryCountT(ConfigData.TheAlarmThresholdEntries)
      then
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
   with Pre => True  --  no contextual analysis is needed
   is
      LocalDesc : AuditTypes.DescriptionT := AuditTypes.NoDescription;
   begin
      if Description'Length < LocalDesc'Length then
         for I in 0 .. Description'Length - 1 loop
            LocalDesc (LocalDesc'First + I) :=
              Description (Description'First + I);
         end loop;
      else
         for I in 0 .. LocalDesc'Length - 1 loop
            LocalDesc (LocalDesc'First + I) :=
              Description (Description'First + I);
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
                      Description        => TheFile)
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
   procedure DeleteLogFile (LogFileEntries : in out LogFileEntryT;
                            Index          : LogFileIndexT)
     with Global  => (In_Out => (AuditSystemFault,
                                 LogFiles,
                                 LogFilesStatus)),
          Depends => ((AuditSystemFault,
                       LogFiles)         =>+ (Index,
                                              LogFiles),
                      (LogFileEntries,
                       LogFilesStatus)   =>+ Index),
          Post    => (for all I in LogFileIndexT'Range =>
                        (if I /= Index then
                           LogFileEntries (I) = LogFileEntries'Old (I)))
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
        with Pre => True  --  no contextual analysis needed
      is
         pragma Unreferenced (E);

         ElementText : ElementTextT := NoElement;
      begin
         ElementText(1..AuditTypes.ElementT_Image(ElementID)'Last) :=
           AuditTypes.ElementT_Image(ElementID);

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
     (LogFileState : in out LogFileStateT;
      ElementID    : in     AuditTypes.ElementT;
      Severity     : in     AuditTypes.SeverityT;
      User         : in     AuditTypes.UserTextT;
      Description  : in     AuditTypes.DescriptionT)
     with Global  => (Input  => Clock.Now,
                      In_Out => (AuditSystemFault,
                                 LogFiles,
                                 LogFilesStatus)),
          Depends => ((AuditSystemFault,
                       LogFiles)         =>+ (Clock.Now,
                                              Description,
                                              ElementID,
                                              LogFileState,
                                              LogFiles,
                                              LogFilesStatus,
                                              Severity,
                                              User),
                      (LogFileState,
                       LogFilesStatus)     =>+ (LogFileState,
                                              LogFilesStatus)),
          Pre     => Valid_NumberLogEntries (LogFileState) and then
                     LogFileState.NumberLogEntries < MaxLogEntries and then
                     (LogFileState.LogFileEntries(LogFileState.CurrentLogFile) < MaxLogFileEntries or
                       LogFileState.UsedLogFiles.Length < LogFileCountT'Last) and then
                     LogFileState.NumberLogEntries =
                       LogEntryCountT(LogFileState.UsedLogFiles.Length - 1) *
                       MaxLogFileEntries + LogFileState.LogFileEntries(LogFileState.CurrentLogFile),
          Post    => LogFileState.NumberLogEntries =
                       LogEntryCountT(LogFileState.UsedLogFiles.Length - 1) *
                       MaxLogFileEntries + LogFileState.LogFileEntries(LogFileState.CurrentLogFile) and
                     LogFileState.NumberLogEntries = LogFileState.NumberLogEntries'Old + 1 and
                     (if LogFileState.LogFileEntries(LogFileState.CurrentLogFile)'Old =
                        MaxLogFileEntries
                      then
                         LogFileState.LogFileEntries(LogFileState.CurrentLogFile) = 1 and
                         LogFileState.UsedLogFiles.Length = LogFileState.UsedLogFiles.Length'Old + 1)
                     and
                     (if LogFileState.LogFileEntries(LogFileState.CurrentLogFile)'Old <
                        MaxLogFileEntries
                      then
                          LogFileState.LogFileEntries(LogFileState.CurrentLogFile) =
                            LogFileState.LogFileEntries(LogFileState.CurrentLogFile)'Old + 1 and
                          LogFileState.UsedLogFiles.Length = LogFileState.UsedLogFiles.Length'Old)
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
        (LogFileState : in out LogFileStateT;
         ElementID    : in     AuditTypes.ElementT;
         Severity     : in     AuditTypes.SeverityT;
         User         : in     AuditTypes.UserTextT;
         Description  : in     AuditTypes.DescriptionT)
        with Global  => (Input  => Clock.Now,
                         In_Out => (AuditSystemFault,
                                    LogFiles)),
             Depends => ((AuditSystemFault,
                          LogFiles)         =>+ (Clock.Now,
                                                 Description,
                                                 ElementID,
                                                 LogFiles,
                                                 LogFileState,
                                                 Severity,
                                                 User),
                          LogFileState      =>+ null),
             Pre     => LogFileState.LogFileEntries(LogFileState.CurrentLogFile) < MaxLogFileEntries,
             Post    => LogFileState.LogFileEntries(LogFileState.CurrentLogFile) =
                          LogFileState.LogFileEntries'Old(LogFileState.CurrentLogFile) + 1 and then
                        LogFileState.CurrentLogFile = LogFileState.CurrentLogFile'Old and then
                        LogFileState.UsedLogFiles = LogFileState.UsedLogFiles'Old and then
                        LogFileState.NumberLogEntries = LogFileState.NumberLogEntries'Old
      is
         TheFile : File.T;
      begin
         TheFile := LogFiles (LogFileState.CurrentLogFile);
         AddElementToFile
           (TheFile     => TheFile,
            ElementID   => ElementID,
            Severity    => Severity,
            User        => User,
            Description => Description);
         LogFiles (LogFileState.CurrentLogFile) := TheFile;

         LogFileState.LogFileEntries(LogFileState.CurrentLogFile) := LogFileState.LogFileEntries(LogFileState.CurrentLogFile) + 1;
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
        (LogFileState : in out LogFileStateT;
         ElementID    : in     AuditTypes.ElementT;
         Severity     : in     AuditTypes.SeverityT;
         User         : in     AuditTypes.UserTextT;
         Description  : in     AuditTypes.DescriptionT)
        with Global  => (Input  => Clock.Now,
                         In_Out => (AuditSystemFault,
                                    LogFiles,
                                    LogFilesStatus)),
             Depends => ((AuditSystemFault,
                          LogFiles)         =>+ (Clock.Now,
                                                 Description,
                                                 ElementID,
                                                 logFileState,
                                                 LogFiles,
                                                 LogFilesStatus,
                                                 Severity,
                                                 User),
                         (LogFileState,
                          LogFilesStatus)   =>+ (LogFileState,
                                                 LogFilesStatus)),
             Pre     => LogFileState.UsedLogFiles.Length < LogFileCountT'Last,
             Post    => LogFileState.UsedLogFiles.Length = LogFileState.UsedLogFiles.Length'Old + 1 and
                          LogFileState.LogFileEntries(LogFileState.CurrentLogFile) = 1 and
                        LogFileState.NumberLogEntries = LogFileState.NumberLogEntries'Old
      is
         TheFile : File.T;

         procedure SetCurrentFileToNextFreeFile (LogFileState : in out LogFileStateT)
         is
         begin
            for I in LogFileIndexT loop
               if LogFilesStatus(I) = Free then
                  LogFileState.CurrentLogFile := I;
                  exit;
               end if;
            end loop;
         end SetCurrentFileToNextFreeFile;

      -------------------------------------------------
      -- AddElementToNextFile
      -------------------------------------------------
      begin
         SetCurrentFileToNextFreeFile (LogFileState);

         LogFilesStatus(LogFileState.CurrentLogFile) := Used;

         -- add currentLogFile' to end of list of UsedLogFiles.
         LogFileState.UsedLogFiles.Length := LogFileState.UsedLogFiles.Length + 1;
         LogFileState.UsedLogFiles.LastI := NextListIndex(LogFileState.UsedLogFiles.LastI);
         LogFileState.UsedLogFiles.List(LogFileState.UsedLogFiles.LastI) := LogFileState.CurrentLogFile;

         TheFile := LogFiles (LogFileState.CurrentLogFile);
         AddElementToFile
           (TheFile     => TheFile,
            ElementID   => ElementID,
            Severity    => Severity,
            User        => User,
            Description => Description);
         LogFiles (LogFileState.CurrentLogFile) := TheFile;

         LogFileState.LogFileEntries(LogFileState.CurrentLogFile) := 1;

      end AddElementToNextFile;

   -------------------------------------------------
   -- AddElementToLogFile
   ------------------------------------------------
   begin
      if LogFileState.LogFileEntries(LogFileState.CurrentLogFile) < MaxLogFileEntries then

         AddElementToCurrentFile
           (LogFileState => LogFileState,
            ElementID    => ElementID,
            Severity     => Severity,
            User         => User,
            Description  => Description);

      else

         AddElementToNextFile
           (LogFileState => LogFileState,
            ElementID    => ElementID,
            Severity     => Severity,
            User         => User,
            Description  => Description);
      end if;

      LogFileState.NumberLogEntries := LogFileState.NumberLogEntries + 1;

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
   procedure TruncateLog
     (LogFileState : in out LogFileStateT;
      Description  : out AuditTypes.DescriptionT)
     with Global  => (Output   => AuditAlarm,
                      In_Out   => (AuditSystemFault,
                                   LogFiles,
                                   LogFilesStatus)),
          Depends => (AuditAlarm         => null,
                      (AuditSystemFault,
                       LogFiles)         =>+ (LogFiles,
                                              LogFileState),
                      Description        => (LogFiles,
                                             LogFileState),
                      (LogFileState,
                       LogFilesStatus)   =>+ LogFileState),
          Pre     => LogFileState.UsedLogFiles.Length >= 1 and
                     LogFileState.UsedLogFiles.Length = LogFileCountT'Last and
                     LogFileState.NumberLogEntries =
                       LogEntryCountT(LogFileState.UsedLogFiles.Length) * MaxLogFileEntries,
          Post    => LogFileState.UsedLogFiles.Length >= 1 and
                     LogFileState.LogFileEntries (LogFileState.CurrentLogFile) =
                       LogFileState.LogFileEntries'Old (LogFileState.CurrentLogFile'Old) and
                     LogFileState.UsedLogFiles.Length = LogFileCountT'Last - 1 and
                     LogFileState.NumberLogEntries =
                       LogEntryCountT(LogFileState.UsedLogFiles.Length) * MaxLogFileEntries
   is
      TheFile : File.T;
      Head    : LogFileIndexT;
   begin
      Head := LogFileState.UsedLogFiles.List(LogFileState.UsedLogFiles.Head);

      -- Make description
      TheFile := LogFiles (Head);
      GetStartAndEndTimeFromFile
        (TheFile     => TheFile,
         Description => Description);
      LogFiles (Head) := TheFile;

      pragma Assume (Head /= LogFileState.CurrentLogFile);

      -- Empty the file.
      DeleteLogFile (LogFileState.LogFileEntries, Head);

      -- remove the head of the usedLogFiles
      LogFileState.UsedLogFiles.Head := NextListIndex (LogFileState.UsedLogFiles.Head);
      LogFileState.UsedLogFiles.Length := LogFileState.UsedLogFiles.Length - 1;

      LogFileState.NumberLogEntries := LogFileState.NumberLogEntries - MaxLogFileEntries;

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
     (LogFileState : in out LogFileStateT;
      ElementID    : in     AuditTypes.ElementT;
      Severity     : in     AuditTypes.SeverityT;
      User         : in     AuditTypes.UserTextT;
      Description  : in     AuditTypes.DescriptionT)
     with Global  => (Input  => Clock.Now,
                      In_Out => (AuditAlarm,
                                 AuditSystemFault,
                                 LogFiles,
                                 LogFilesStatus)),
          Depends => (AuditAlarm         =>+ LogFileState,
                      (AuditSystemFault,
                       LogFiles)         =>+ (Clock.Now,
                                              Description,
                                              ElementID,
                                              LogFileState,
                                              LogFiles,
                                              LogFilesStatus,
                                              Severity,
                                              User),
                      (LogFilesStatus,
                       LogFileState)     => (LogFileState,
                                             LogFilesStatus)),
          Pre  => LogFileState.UsedLogFiles.Length >= 1 and then
                  LogFileState.NumberLogEntries =
                    LogEntryCountT(LogFileState.UsedLogFiles.Length - 1) *
                    MaxLogFileEntries + LogFileState.LogFileEntries(LogFileState.CurrentLogFile),
          Post => LogFileState.UsedLogFiles.Length >= 1 and
                  LogFileState.NumberLogEntries =
                    LogEntryCountT(LogFileState.UsedLogFiles.Length - 1) *
                    MaxLogFileEntries + LogFileState.LogFileEntries(LogFileState.CurrentLogFile)
   is
      TruncateDescription : AuditTypes.DescriptionT;
   begin
      if LogFileState.LogFileEntries(LogFileState.CurrentLogFile) = MaxLogFileEntries
        and LogFileState.UsedLogFiles.Length = LogFileCountT'Last
      then

         TruncateLog(LogFileState => LogFileState,
                     Description  => TruncateDescription);

         AddElementToLogFile
           (LogFileState => LogFileState,
            ElementID    => AuditTypes.TruncateLog,
            Severity     => AuditTypes.Critical,
            User         => AuditTypes.NoUser,
            Description  => TruncateDescription);

      end if;

      AddElementToLogFile
        (LogFileState => LogFileState,
         ElementID    => ElementID,
         Severity     => Severity,
         User         => User,
         Description  => Description);

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
                                         LogFilesStatus,
                                         LogFileState),
                              In_Out => LogFiles),
          Refined_Depends => (AuditAlarm         => (ConfigData.State,
                                                     LogFiles),
                              (AuditSystemFault,
                               LogFiles,
                               LogFilesStatus,
                               LogFileState)     => LogFiles),
          Refined_Post    => LogFileState.UsedLogFiles.Length >= 1 and
                             LogFileState.NumberLogEntries =
                               LogEntryCountT(LogFileState.UsedLogFiles.Length - 1) *
                               MaxLogFileEntries +
                               LogFileState.LogFileEntries(LogFileState.CurrentLogFile)
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
     procedure SetFileDetails (LogFileEntries : out LogFileEntryT)
       with Global  => (Output => (FileAges,
                                   LogFilesStatus),
                        In_Out => (AuditSystemFault,
                                   LogFiles)),
            Depends => ((AuditSystemFault,
                         LogFiles)         =>+ LogFiles,
                        (FileAges,
                         LogFileEntries,
                         LogFilesStatus)   => LogFiles)
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
                            Status)         => (I,
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

        pragma Warnings (Off);
        for I in LogFileIndexT loop
           GetFileDetails(I);
           LogFilesStatus(I) := Status;
           LogFiles(I)       := FileH;
           FileAges(I)       := FirstTime;
           LogFileEntries(I) := NumberEntries;
        end loop;
        pragma Warnings (On);
     end SetFileDetails;

   ------------------------------------------------------------------
   -- begin Init
   ------------------------------------------------------------------
   begin
      File.CreateDirectory(DirName => LogDirectory,
                           Success => OK);

      AuditSystemFault := not OK;

      SetFileDetails (LogFileState.LogFileEntries);

      -- Now put the used files in order in the list.

      LogFileState.UsedLogFiles := EmptyList;
      for I in LogFileIndexT loop
         pragma Loop_Invariant (LogFileState.UsedLogFiles.Length < I);
         pragma Loop_Invariant (if LogFileState.UsedLogFiles.Length > 0 then LogFileState.UsedLogFiles.LastI < I);

         if LogFilesStatus(I) = Used then
            if LogFileState.UsedLogFiles.Length = 0 then
               -- easy case list currently empty
               LogFileState.UsedLogFiles.Head := LogFileIndexT'First;
               LogFileState.UsedLogFiles.LastI := LogFileIndexT'First;
               LogFileState.UsedLogFiles.Length := 1;
               LogFileState.UsedLogFiles.List(LogFileState.UsedLogFiles.Head) := I;
            else
               for J in LogFileIndexT range 1..LogFileState.UsedLogFiles.LastI loop
                  pragma Loop_Invariant (LogFileState.UsedLogFiles.Length in 1 .. I-1);
                  pragma Loop_Invariant (if LogFileState.UsedLogFiles.Length > 0 then LogFileState.UsedLogFiles.LastI < I);

                  if AgeLessThan(FileAges(I), FileAges(LogFileState.UsedLogFiles.List(J))) then
                     -- this is where the new entry goes.
                     -- move all other entries up the list to make room
                     LogFileState.UsedLogFiles.LastI  := LogFileState.UsedLogFiles.LastI + 1;
                     LogFileState.UsedLogFiles.Length := LogFileState.UsedLogFiles.Length + 1;
                     for K in reverse LogFileIndexT
                       range J + 1..LogFileState.UsedLogFiles.LastI
                     loop
                        LogFileState.UsedLogFiles.List(K) := LogFileState.UsedLogFiles.List(K - 1);
                     end loop;
                     LogFileState.UsedLogFiles.List(J) := I;
                     exit;
                  end if;
                  if J = LogFileState.UsedLogFiles.LastI then
                     -- entry goes at the end
                     LogFileState.UsedLogFiles.LastI  := LogFileState.UsedLogFiles.LastI + 1;
                     LogFileState.UsedLogFiles.Length := LogFileState.UsedLogFiles.Length + 1;
                     LogFileState.UsedLogFiles.List(LogFileState.UsedLogFiles.LastI) := I;
                     exit;
                  end if;
               end loop;
            end if;
         end if;
      end loop;

      if LogFileState.UsedLogFiles.Length = 0 then
         LogFileState.CurrentLogFile := LogFileIndexT'First;
         -- The current file is the first used file.
         LogFileState.UsedLogFiles.Head := LogFileIndexT'First;
         LogFileState.UsedLogFiles.LastI := LogFileIndexT'First;
         LogFileState.UsedLogFiles.Length := 1;
         LogFileState.UsedLogFiles.List(LogFileState.UsedLogFiles.Head) := LogFileState.CurrentLogFile;
         LogFilesStatus(LogFileState.CurrentLogFile) := Used;
      else
         LogFileState.CurrentLogFile := LogFileState.UsedLogFiles.List(LogFileState.UsedLogFiles.LastI);
      end if;

      LogFileState.NumberLogEntries := LogEntryCountT(LogFileState.UsedLogFiles.Length - 1) *
        MaxLogFileEntries + LogFileState.LogFileEntries(LogFileState.CurrentLogFile);

      AuditAlarm := AlarmTypes.Silent;
      CheckLogAlarm (LogFileState);

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
                                         LogFileState,
                                         LogFiles,
                                         LogFilesStatus)),
          Refined_Depends => ((AuditAlarm,
                               LogFilesStatus,
                               LogFileState)     => (AuditAlarm,
                                                     ConfigData.State,
                                                     LogFileState,
                                                     LogFilesStatus),
                              (AuditSystemFault,
                               LogFiles)         =>+ (AuditAlarm,
                                                      Clock.Now,
                                                      ConfigData.State,
                                                      Description,
                                                      ElementID,
                                                      LogFileState,
                                                      LogFiles,
                                                      LogFilesStatus,
                                                      Severity,
                                                      User)),
          --  Refined_Pre     => (UsedLogFiles.Length >= 1 and then
          --                        NumberLogEntries =
          --                        LogEntryCountT(UsedLogFiles.Length - 1) * MaxLogFileEntries +
          --                        LogFileEntries(CurrentLogFile)),
          --  This has been substituted by a call to Valid_NumberLogEntries
          --  at the specs
          Refined_Post    => LogFileState.UsedLogFiles.Length >= 1 and
                             LogFileState.NumberLogEntries =
                               LogEntryCountT(LogFileState.UsedLogFiles.Length - 1) *
                               MaxLogFileEntries +
                               LogFileState.LogFileEntries(LogFileState.CurrentLogFile)
   is
      OldAlarm : AlarmTypes.StatusT;
   begin
      OldAlarm := AuditAlarm;

      AddElementToLogFileWithTruncateChecks
        (LogFileState => LogFileState,
         ElementID    => ElementID,
         Severity     => Severity,
         User         => User,
         Description  => ConvertToAuditDescription (Description));

      CheckLogAlarm (LogFileState);

      if OldAlarm /= AuditAlarm then
         -- This will always raise alarms not clear them
         AddElementToLogFileWithTruncateChecks
           (LogFileState => LogFileState,
            ElementID    => AuditTypes.AuditAlarmRaised,
            Severity     => AuditTypes.Warning,
            User         => AuditTypes.NoUser,
            Description  => AuditTypes.NoDescription);
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
                                         LogFileState,
                                         LogFiles,
                                         LogFilesStatus)),
          Refined_Depends => (Archive            => (LogFileState,
                                                     LogFiles),
                              (AuditAlarm,
                               LogFileState,
                               LogFilesStatus)   => (AuditAlarm,
                                                     ConfigData.State,
                                                     LogFileState,
                                                     LogFiles,
                                                     LogFilesStatus),
                              (AuditSystemFault,
                               LogFiles)         =>+ (AuditAlarm,
                                                      Clock.Now,
                                                      ConfigData.State,
                                                      LogFileState,
                                                      LogFiles,
                                                      LogFilesStatus,
                                                      User)),
          --  Refined_Pre     => (UsedLogFiles.Length >= 1 and then
          --                        NumberLogEntries =
          --                        LogEntryCountT(UsedLogFiles.Length - 1) * MaxLogFileEntries +
          --                        LogFileEntries(CurrentLogFile)),
          --  This has been substituted by a call to Valid_NumberLogEntries
          --  at the specs
          Refined_Post    => LogFileState.UsedLogFiles.Length >= 1 and
                             LogFileState.NumberLogEntries =
                               LogEntryCountT(LogFileState.UsedLogFiles.Length - 1) *
                               MaxLogFileEntries +
                               LogFileState.LogFileEntries(LogFileState.CurrentLogFile)
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

      if LogFileState.UsedLogFiles.Length = 0 or
        (LogFileState.UsedLogFiles.Length = 1 and
           LogFileState.LogFileEntries(LogFileState.UsedLogFiles.List(LogFileState.UsedLogFiles.Head))
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
         FileIndexInUsedList := LogFileState.UsedLogFiles.Head;

         while ArchivedFileCount < MaxNumberArchivableFiles
           and ArchivedFileCount < LogFileState.UsedLogFiles.Length
         loop
            pragma Loop_Invariant
              (LogFileState.NumberLogEntries =
                 LogEntryCountT(LogFileState.UsedLogFiles.Length - 1) * MaxLogFileEntries +
                 LogFileState.LogFileEntries(LogFileState.CurrentLogFile));

            FileIndex := LogFileState.UsedLogFiles.List(FileIndexInUsedList);
            exit when LogFileState.LogFileEntries(FileIndex) < MaxLogFileEntries;

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

      -- As we always add at least one element to the log the CurrentLogFile
      -- cannot be archived.

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
                                         LogFileState,
                                         LogFiles,
                                         LogFilesStatus)),
          Refined_Depends => ((AuditAlarm,
                               LogFileState,
                               LogFilesStatus)   => (AuditAlarm,
                                                     ConfigData.State,
                                                     LogFileState,
                                                     LogFilesStatus),
                              (AuditSystemFault,
                               LogFiles)         =>+ (AuditAlarm,
                                                      Clock.Now,
                                                      ConfigData.State,
                                                      LogFileState,
                                                      LogFiles,
                                                      LogFilesStatus,
                                                      User)),
          --  Refined_Pre     => (UsedLogFiles.Length >= 1 and then
          --                        NumberLogEntries =
          --                        LogEntryCountT(UsedLogFiles.Length - 1) * MaxLogFileEntries +
          --                        LogFileEntries(CurrentLogFile)),
          --  This has been substituted by a call to Valid_NumberLogEntries
          --  at the specs
          Refined_Post    => LogFileState.UsedLogFiles.Length >= 1 and
                             LogFileState.NumberLogEntries =
                               LogEntryCountT(LogFileState.UsedLogFiles.Length - 1) *
                               MaxLogFileEntries +
                               LogFileState.LogFileEntries(LogFileState.CurrentLogFile)
   is
      OldAlarm : AlarmTypes.StatusT;
   begin
      -- Note the CurrentLogFile cannot be Archived.

      while LogFileState.UsedLogFiles.Length > 1 loop
         --  pragma Loop_Invariant
         --    (UsedLogFiles.Length > 1 and then
         --     NumberLogEntries =
         --       LogEntryCountT(UsedLogFiles.Length - 1) * MaxLogFileEntries +
         --       LogFileEntries(CurrentLogFile));
         exit when LogFilesStatus(LogFileState.UsedLogFiles.List(LogFileState.UsedLogFiles.Head))
           /= Archived;
         pragma Loop_Invariant
           (LogFileState.UsedLogFiles.Length > 1 and
            LogFilesStatus(LogFileState.UsedLogFiles.List(LogFileState.UsedLogFiles.Head))
              = Archived and
            LogFileState.NumberLogEntries =
              LogEntryCountT(LogFileState.UsedLogFiles.Length - 1) * MaxLogFileEntries +
              LogFileState.LogFileEntries(LogFileState.CurrentLogFile));

         pragma Assume (LogFileState.UsedLogFiles.List(LogFileState.UsedLogFiles.Head) /= LogFileState.CurrentLogFile);

         -- Empty the archived file.
         DeleteLogFile (LogFileState.LogFileEntries, LogFileState.UsedLogFiles.List(LogFileState.UsedLogFiles.Head));

         LogFileState.UsedLogFiles.Length := LogFileState.UsedLogFiles.Length - 1;
         LogFileState.UsedLogFiles.Head := NextListIndex (LogFileState.UsedLogFiles.Head);

         LogFileState.NumberLogEntries := LogFileState.NumberLogEntries - MaxLogFileEntries;

      end loop;

      OldAlarm := AuditAlarm;

      AuditAlarm := AlarmTypes.Silent;
      CheckLogAlarm (LogFileState);

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

      pragma Warnings (Off);
      DeleteArchiveFile;
      pragma Warnings (On);

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

      pragma Warnings (Off);
      DeleteArchiveFile;
      pragma Warnings (On);

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
