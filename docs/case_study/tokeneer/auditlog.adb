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
--    Implementation of the AuditLog.
--
------------------------------------------------------------------
with Clock;
with ConfigData;

with AlarmTypes;
use type AlarmTypes.StatusT;

package body AuditLog
--# own State is AuditAlarm,
--#              CurrentLogFile,
--#              UsedLogFiles,
--#              LogFileEntries,
--#              LogFilesStatus,
--#              NumberLogEntries,
--#              AuditSystemFault &
--#    FileState is LogFiles;
is

   ------------------------------------------------------------------
   -- Private Operations
   --
   ------------------------------------------------------------------

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
   function NextListIndex(Value : LogFileIndexT) return  LogFileIndexT
   is
      Result : LogFileIndexT;
   begin
      if Value = LogFileIndexT'Last then
         Result := LogFileIndexT'First;
      else
         Result := Value + 1;
      end if;
      return Result;
   end NextListIndex;

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
   --# global in     NumberLogEntries;
   --#        in     ConfigData.State;
   --#        in out AuditAlarm;
   --# derives AuditAlarm from *,
   --#                         NumberLogEntries,
   --#                         ConfigData.State;
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
   --   Implementation Notes:
   --      Hidden as uses slicing
   --
   ------------------------------------------------------------------
   function ConvertToAuditDescription(Description : String)
                                      return AuditTypes.DescriptionT
   is
      --# hide ConvertToAuditDescription;
      LocalDesc : AuditTypes.DescriptionT := AuditTypes.NoDescription;
   begin
      if Description'Last < LocalDesc'Last then
         LocalDesc(1 .. Description'Last) := Description;
      else
         LocalDesc := Description(1 .. LocalDesc'Last);
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
     --# global in out AuditSystemFault;
     --# derives AuditSystemFault,
     --#         TheFile          from *,
     --#                               TheFile &
     --#         Description      from TheFile;
   is
      OK : Boolean;
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
      --       Hidden from SPARK because of use of & in non-Static context.
      --
      ------------------------------------------------------------------
      function ConvertTimesToText return AuditTypes.DescriptionT
        --# global FirstTime,
        --#        LastTime,
        --#        TimeOK;
      is
         --# hide ConvertTimesToText;
         Descr : AuditTypes.DescriptionT;
      begin
         if TimeOK then
            Descr :=
              ConvertToAuditDescription("From: " & FirstTime & " to: " & LastTime);
         else
            Descr :=
              ConvertToAuditDescription("Error obtaining times from file. Best estimate is from: "
                                        & FirstTime & " to: " & LastTime);
         end if;

         return Descr;

      end ConvertTimesToText;

   -------------------------------------------------------------------
   -- begin GetStartAndEndTimeFromFile
   -------------------------------------------------------------------
   begin

      FirstTime := Clock.PrintTime(Clock.ZeroTime);
      LastTime := Clock.PrintTime(Clock.ZeroTime);

      if File.Exists( TheFile => TheFile) then
         File.OpenRead( TheFile => TheFile,
                        Success => OK );

         AuditSystemFault := AuditSystemFault or not OK;

         if OK then
            -- get the age of the first element
            -- time is the first field on the line
            File.GetString( TheFile => TheFile,
                            Text    => FirstTime,
                            Stop    => TimeCount);

            if TimeCount /= FirstTime'Last then
               -- Time was corrupt
               TimeOK := False;
            end if;

            File.SkipLine(TheFile, MaxLogFileEntries - 1 );

            -- get the age of the last element
            File.GetString( TheFile => TheFile,
                            Text    => LastTime,
                            Stop    => TimeCount);

            if TimeCount /= LastTime'Last then
               -- Time was corrupt
               TimeOK := False;
            end if;

        end if;

         File.Close( TheFile => TheFile,
                     Success => OK );

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
     --# global in out AuditSystemFault;
     --# derives AuditSystemFault,
     --#         TheFile,
     --#         Description      from *,
     --#                               TheFile;
   is
      OK : Boolean;
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
      --       Hidden from SPARK because of use of & in non-Static context.
      --
      ------------------------------------------------------------------
      function OverwriteTimeInText(Description : AuditTypes.DescriptionT )
                                   return AuditTypes.DescriptionT
        --# global LastTime,
        --#        TimeOK;
      is
         --# hide OverwriteTimeInText;
         Descr : AuditTypes.DescriptionT;
         FirstTime : Clock.TimeTextT;
         Offset : Positive;
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
         FirstTime := Description(Offset + FirstTime'First ..
                                  Offset + FirstTime'Last);

         if BothTimesOK then
            Descr :=
              ConvertToAuditDescription("From: " & FirstTime & " to: " & LastTime);
         else
            Descr :=
              ConvertToAuditDescription("Error obtaining times from file. Best estimate is from: "
                                        & FirstTime & " to: " & LastTime);
         end if;

         return Descr;

      end OverwriteTimeInText;

   -------------------------------------------------------------------
   -- begin UpdateEndTimeFromFile
   -------------------------------------------------------------------
   begin

      LastTime := Clock.PrintTime(Clock.ZeroTime);

      if File.Exists( TheFile => TheFile) then
         File.OpenRead( TheFile => TheFile,
                        Success => OK );

         AuditSystemFault := AuditSystemFault or not OK;

         if OK then
            File.SkipLine(TheFile, MaxLogFileEntries - 1 );

            -- get the age of the last element
            -- the time is the first field on the line
            File.GetString( TheFile => TheFile,
                            Text    => LastTime,
                            Stop    => TimeCount);

            if TimeCount /= LastTime'Last then
               -- Time was corrupt
               TimeOK := False;
            end if;

        end if;

         File.Close( TheFile => TheFile,
                     Success => OK );

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
   --# derives ;
   is
      --# hide DeleteArchiveFile;
      Archive : File.T;
      Unused : Boolean;
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
   procedure DeleteLogFile ( Index : LogFileIndexT)
   --# global in out AuditSystemFault;
   --#        in out LogFiles;
   --#        in out LogFilesStatus;
   --#        in out LogFileEntries;
   --# derives AuditSystemFault,
   --#         LogFiles         from *,
   --#                               LogFiles,
   --#                               Index &
   --#         LogFilesStatus,
   --#         LogFileEntries   from *,
   --#                               Index;
   is
      OK : Boolean;
      TheFile : File.T;
   begin

      TheFile := LogFiles (Index);

      File.OpenRead(TheFile => TheFile,
                    Success => OK);
      AuditSystemFault := AuditSystemFault and not OK;
      File.Delete(TheFile => TheFile,
                  Success => OK);
      AuditSystemFault := AuditSystemFault and not OK;

      LogFiles( Index) := TheFile;

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
                TheFile      : in out File.T;
                ElementID    : in     AuditTypes.ElementT;
                Severity     : in     AuditTypes.SeverityT;
                User         : in     AuditTypes.UserTextT;
                Description  : in     AuditTypes.DescriptionT)
   --# global in     Clock.Now;
   --#        in out AuditSystemFault;
   --# derives AuditSystemFault,
   --#         TheFile          from *,
   --#                               TheFile,
   --#                               Description,
   --#                               Clock.Now,
   --#                               ElementID,
   --#                               Severity,
   --#                               User;
   is
      OK : Boolean;
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
      function NameOfType (E : AuditTypes.ElementT ) return ElementTextT
      is
      --# hide NameOfType;

         ElementText : ElementTextT := NoElement;

      begin

         ElementText(1.. AuditTypes.ElementT'Image(ElementID)'Last)
           := AuditTypes.ElementT'Image(ElementID);

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
           File.Create( TheFile => TheFile,
                        Success => OK);

      end if;

      if OK then
         -- Write Time
         File.PutString( TheFile => TheFile,
                         Text    => Clock.PrintTime(Now),
                         Stop    => 0 );

         File.PutString( TheFile => TheFile,
                         Text    => ", ",
                         Stop    => 0);

         -- Write Severity
         File.PutInteger( TheFile => TheFile,
                          Item   => AuditTypes.SeverityT'Pos(Severity)+ 1,
                          Width  => 1);

         File.PutString( TheFile => TheFile,
                         Text    => ", ",
                         Stop    => 0);

         -- Write type
         File.PutInteger( TheFile => TheFile,
                          Item    => AuditTypes.ElementT'Pos(ElementID),
                          Width   => 2);

         File.PutString( TheFile => TheFile,
                         Text    => ", ",
                         Stop    => 0);

         File.PutString( TheFile => TheFile,
                         Text   => NameOfType (ElementID),
                         Stop => 0);

         File.PutString( TheFile => TheFile,
                         Text    => ", ",
                         Stop    => 0);

         -- Write user
         File.PutString( TheFile => TheFile,
                         Text    => User,
                         Stop    => 0);

         File.PutString( TheFile => TheFile,
                         Text    => ", ",
                         Stop    => 0);

         -- Write description
         File.PutString( TheFile => TheFile,
                         Text    => Description,
                         Stop    => 0);

         File.NewLine( TheFile => TheFile,
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
     ( ElementID    : in     AuditTypes.ElementT;
       Severity     : in     AuditTypes.SeverityT;
       User         : in     AuditTypes.UserTextT;
       Description  : in     AuditTypes.DescriptionT);
   pragma Precondition
     (UsedLogFiles.Length >= 1 and then
      NumberLogEntries < MaxLogEntries and then
        (LogFileEntries(CurrentLogFile) < MaxLogFileEntries or else
         UsedLogFiles.Length < LogFileCountT'Last) and then
      NumberLogEntries =
        LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
        LogFileEntries(CurrentLogFile));
   pragma Postcondition
     (NumberLogEntries =
        LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
        LogFileEntries(CurrentLogFile) and then
      NumberLogEntries = NumberLogEntries'Old + 1 and then
        ((LogFileEntries(CurrentLogFile)'Old = MaxLogFileEntries) <=
         (LogFileEntries(CurrentLogFile) = 1 and then
            UsedLogFiles.Length = UsedLogFiles.Length'Old + 1)) and then
        ((LogFileEntries(CurrentLogFile)'Old < MaxLogFileEntries) <=
         (LogFileEntries(CurrentLogFile) =
              LogFileEntries(CurrentLogFile)'Old + 1 and then
            UsedLogFiles.Length = UsedLogFiles.Length'Old)));

   procedure AddElementToLogFile
     ( ElementID    : in     AuditTypes.ElementT;
       Severity     : in     AuditTypes.SeverityT;
       User         : in     AuditTypes.UserTextT;
       Description  : in     AuditTypes.DescriptionT)
     --# global in     Clock.Now;
     --#        in out NumberLogEntries;
     --#        in out AuditSystemFault;
     --#        in out LogFiles;
     --#        in out LogFilesStatus;
     --#        in out LogFileEntries;
     --#        in out CurrentLogFile;
     --#        in out UsedLogFiles;
     --# derives AuditSystemFault,
     --#         LogFiles         from *,
     --#                               Description,
     --#                               LogFiles,
     --#                               LogFilesStatus,
     --#                               LogFileEntries,
     --#                               Clock.Now,
     --#                               ElementID,
     --#                               Severity,
     --#                               User,
     --#                               CurrentLogFile &
     --#         LogFilesStatus,
     --#         LogFileEntries,
     --#         CurrentLogFile,
     --#         UsedLogFiles     from *,
     --#                               LogFilesStatus,
     --#                               LogFileEntries,
     --#                               CurrentLogFile &
     --#         NumberLogEntries from *;
     --# pre NumberLogEntries < MaxLogEntries and
     --#     (LogFileEntries(CurrentLogFile) < MaxLogFileEntries or
     --#                 UsedLogFiles.Length < LogFileCountT'Last) and
     --#     NumberLogEntries = LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
     --#                        LogFileEntries(CurrentLogFile);
     --#
     --# post NumberLogEntries = LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
     --#                        LogFileEntries(CurrentLogFile) and
     --#      NumberLogEntries = NumberLogEntries~ + 1 and
     --#      (LogFileEntries~(CurrentLogFile~) = MaxLogFileEntries ->
     --#         (LogFileEntries(CurrentLogFile) = 1 and
     --#          UsedLogFiles.Length = UsedLogFiles~.Length + 1)) and
     --#      (LogFileEntries~(CurrentLogFile~) < MaxLogFileEntries ->
     --#         (LogFileEntries(CurrentLogFile) = LogFileEntries~(CurrentLogFile~) + 1 and
     --#          UsedLogFiles.Length = UsedLogFiles~.Length)) ;
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
        (ElementID    : in     AuditTypes.ElementT;
         Severity     : in     AuditTypes.SeverityT;
         User         : in     AuditTypes.UserTextT;
         Description  : in     AuditTypes.DescriptionT);
      pragma Precondition
        (LogFileEntries(CurrentLogFile) < MaxLogFileEntries);
      pragma Postcondition
        (LogFileEntries(CurrentLogFile) =
           LogFileEntries(CurrentLogFile)'Old + 1);

      procedure AddElementToCurrentFile
        (ElementID    : in     AuditTypes.ElementT;
         Severity     : in     AuditTypes.SeverityT;
         User         : in     AuditTypes.UserTextT;
         Description  : in     AuditTypes.DescriptionT)
        --# global in     Clock.Now;
        --#        in     CurrentLogFile;
        --#        in out AuditSystemFault;
        --#        in out LogFiles;
        --#        in out LogFileEntries;
        --# derives AuditSystemFault,
        --#         LogFiles         from *,
        --#                               Description,
        --#                               LogFiles,
        --#                               Clock.Now,
        --#                               ElementID,
        --#                               Severity,
        --#                               User,
        --#                               CurrentLogFile &
        --#         LogFileEntries   from *,
        --#                               CurrentLogFile;
        --# pre LogFileEntries(CurrentLogFile) < MaxLogFileEntries;
        --# post LogFileEntries(CurrentLogFile) =
        --#             LogFileEntries~(CurrentLogFile) + 1;

      is
         TheFile : File.T ;
      begin
         TheFile := LogFiles (CurrentLogFile);
         AddElementToFile
           (TheFile => TheFile,
            ElementID    => ElementID,
            Severity     => Severity,
            User         => User,
            Description  => Description);
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
        (ElementID    : in     AuditTypes.ElementT;
         Severity     : in     AuditTypes.SeverityT;
         User         : in     AuditTypes.UserTextT;
         Description  : in     AuditTypes.DescriptionT);
      pragma Precondition (UsedLogFiles.Length < LogFileCountT'Last);
      pragma Postcondition
        (UsedLogFiles.Length = UsedLogFiles.Length'Old + 1 and then
         LogFileEntries(CurrentLogFile) = 1);

      procedure AddElementToNextFile
        (ElementID    : in     AuditTypes.ElementT;
         Severity     : in     AuditTypes.SeverityT;
         User         : in     AuditTypes.UserTextT;
         Description  : in     AuditTypes.DescriptionT)
        --# global in     Clock.Now;
        --#        in out AuditSystemFault;
        --#        in out LogFiles;
        --#        in out LogFilesStatus;
        --#        in out LogFileEntries;
        --#        in out CurrentLogFile;
        --#        in out UsedLogFiles;
        --# derives AuditSystemFault,
        --#         LogFiles         from *,
        --#                               Description,
        --#                               LogFiles,
        --#                               LogFilesStatus,
        --#                               Clock.Now,
        --#                               ElementID,
        --#                               Severity,
        --#                               User,
        --#                               CurrentLogFile &
        --#         LogFilesStatus,
        --#         LogFileEntries,
        --#         CurrentLogFile,
        --#         UsedLogFiles     from *,
        --#                               LogFilesStatus,
        --#                               CurrentLogFile;
        --# pre UsedLogFiles.Length < LogFileCountT'Last;
        --# post  UsedLogFiles.Length = UsedLogFiles~.Length + 1 and
        --#                        LogFileEntries(CurrentLogFile) = 1;
      is
         TheFile : File.T ;

         procedure SetCurrentFileToNextFreeFile
         --# global in     LogFilesStatus;
         --#        in out CurrentLogFile;
         --# derives CurrentLogFile from *,
         --#                             LogFilesStatus;
         is
         begin
            for I in LogFileIndexT loop
               --# assert I in LogFileIndexT;
               pragma Loop_Invariant (I in LogFileIndexT);
               if LogFilesStatus(I) = Free then
                  CurrentLogFile := I;
                  exit;
               end if;
            end loop;
         end SetCurrentFileToNextFreeFile;

         -------------------------------------------------
         -- AddElementToNextFile
         ------------------------------------------------
      begin

         SetCurrentFileToNextFreeFile;

         LogFilesStatus( CurrentLogFile) := Used;

         -- add currentLogFile' to end of list of UsedLogFiles.
         UsedLogFiles.Length := UsedLogFiles.Length + 1;
         UsedLogFiles.LastI := NextListIndex( UsedLogFiles.LastI);
         UsedLogFiles.List(UsedLogFiles.LastI) := CurrentLogFile;

         TheFile := LogFiles (CurrentLogFile);
         AddElementToFile
           (TheFile => TheFile,
            ElementID    => ElementID,
            Severity     => Severity,
            User         => User,
            Description  => Description);
         LogFiles (CurrentLogFile) := TheFile;

         LogFileEntries(CurrentLogFile) := 1;

      end AddElementToNextFile;


      -------------------------------------------------
      -- AddElementToLogFile
      ------------------------------------------------
   begin

      if LogFileEntries(CurrentLogFile) < MaxLogFileEntries then

         AddElementToCurrentFile
           ( ElementID   => ElementID,
             Severity    => Severity,
             User        => User,
             Description => Description);

      else

         --# check LogFileEntries(CurrentLogFile) = MaxLogFileEntries;
         pragma Assert (LogFileEntries(CurrentLogFile) = MaxLogFileEntries);

         AddElementToNextFile
           ( ElementID   => ElementID,
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
   procedure TruncateLog( Description : out AuditTypes.DescriptionT);
   pragma Precondition
     (UsedLogFiles.Length = LogFileCountT'Last and then
      NumberLogEntries =
        LogEntryCountT(UsedLogFiles.Length)*MaxLogFileEntries);
   pragma Postcondition
     (UsedLogFiles.Length = LogFileCountT'Last - 1 and then
      NumberLogEntries =
        LogEntryCountT(UsedLogFiles.Length)*MaxLogFileEntries);

   procedure TruncateLog( Description : out AuditTypes.DescriptionT)
     --# global in out NumberLogEntries;
     --#        in out AuditSystemFault;
     --#        in out LogFiles;
     --#        in out LogFilesStatus;
     --#        in out LogFileEntries;
     --#        in out UsedLogFiles;
     --#           out AuditAlarm;
     --# derives NumberLogEntries,
     --#         UsedLogFiles     from * &
     --#         AuditSystemFault,
     --#         LogFiles         from *,
     --#                               LogFiles,
     --#                               UsedLogFiles &
     --#         LogFilesStatus,
     --#         LogFileEntries   from *,
     --#                               UsedLogFiles &
     --#         AuditAlarm       from  &
     --#         Description      from LogFiles,
     --#                               UsedLogFiles;
     --# pre UsedLogFiles.Length = LogFileCountT'Last and
     --#  NumberLogEntries = LogEntryCountT(UsedLogFiles.Length)*MaxLogFileEntries;
     --# post UsedLogFiles.Length = LogFileCountT'Last - 1 and
     --#  NumberLogEntries = LogEntryCountT(UsedLogFiles.Length)*MaxLogFileEntries;
   is
      TheFile : File.T ;
      Head : LogFileIndexT;

   begin

      Head := UsedLogFiles.List(UsedLogFiles.Head);

      -- Make description
      TheFile := LogFiles (Head);
      GetStartAndEndTimeFromFile
        ( TheFile     => TheFile,
          Description => Description);
      LogFiles (Head) := TheFile;

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
     ( ElementID    : in     AuditTypes.ElementT;
       Severity     : in     AuditTypes.SeverityT;
       User         : in     AuditTypes.UserTextT;
       Description  : in     AuditTypes.DescriptionT);
   pragma Precondition
     (UsedLogFiles.Length >= 1 and then
      NumberLogEntries =
        LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
        LogFileEntries(CurrentLogFile));
   pragma Postcondition
     (UsedLogFiles.Length >= 1 and then
      NumberLogEntries =
        LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
        LogFileEntries(CurrentLogFile));

   procedure AddElementToLogFileWithTruncateChecks
     ( ElementID    : in     AuditTypes.ElementT;
       Severity     : in     AuditTypes.SeverityT;
       User         : in     AuditTypes.UserTextT;
       Description  : in     AuditTypes.DescriptionT)
     --# global in     Clock.Now;
     --#        in out AuditAlarm;
     --#        in out NumberLogEntries;
     --#        in out AuditSystemFault;
     --#        in out LogFiles;
     --#        in out LogFilesStatus;
     --#        in out LogFileEntries;
     --#        in out CurrentLogFile;
     --#        in out UsedLogFiles;
     --# derives AuditAlarm,
     --#         NumberLogEntries,
     --#         LogFilesStatus   from *,
     --#                               LogFileEntries,
     --#                               CurrentLogFile,
     --#                               UsedLogFiles &
     --#         AuditSystemFault,
     --#         LogFiles         from *,
     --#                               Description,
     --#                               LogFiles,
     --#                               LogFilesStatus,
     --#                               LogFileEntries,
     --#                               Clock.Now,
     --#                               ElementID,
     --#                               Severity,
     --#                               User,
     --#                               CurrentLogFile,
     --#                               UsedLogFiles &
     --#         LogFileEntries,
     --#         CurrentLogFile,
     --#         UsedLogFiles     from LogFilesStatus,
     --#                               LogFileEntries,
     --#                               CurrentLogFile,
     --#                               UsedLogFiles;
     --# pre NumberLogEntries = LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
     --#                        LogFileEntries(CurrentLogFile);
     --# post NumberLogEntries = LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
     --#                        LogFileEntries(CurrentLogFile);
   is
      TruncateDescription : AuditTypes.DescriptionT;

   begin
      if LogFileEntries(CurrentLogFile) = MaxLogFileEntries
        and UsedLogFiles.Length = LogFileCountT'Last then

         TruncateLog(Description => TruncateDescription);

         --# assert NumberLogEntries =
         --#     LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
         --#     LogFileEntries(CurrentLogFile) and
         --#     LogFileEntries(CurrentLogFile) = MaxLogFileEntries and
         --#     UsedLogFiles.Length = LogFileCountT'Last - 1;
         pragma Assert_And_Cut
           (NumberLogEntries =
              LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
              LogFileEntries(CurrentLogFile) and then
            LogFileEntries(CurrentLogFile) = MaxLogFileEntries and then
            UsedLogFiles.Length = LogFileCountT'Last - 1);

         AddElementToLogFile
           ( ElementID   => AuditTypes.TruncateLog,
             Severity    => AuditTypes.Critical,
             User        => AuditTypes.NoUser,
             Description => TruncateDescription);

         --# assert NumberLogEntries =
         --#     LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
         --#     LogFileEntries(CurrentLogFile) and
         --#     LogFileEntries(CurrentLogFile) = 1  and
         --#     UsedLogFiles.Length = LogFileCountT'Last;
         pragma Assert_And_Cut
           (NumberLogEntries =
              LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
              LogFileEntries(CurrentLogFile) and then
            LogFileEntries(CurrentLogFile) = 1 and then
            UsedLogFiles.Length = LogFileCountT'Last);

      end if;

         --# assert NumberLogEntries =
         --#     LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
         --#     LogFileEntries(CurrentLogFile) and
         --#     (LogFileEntries(CurrentLogFile) < MaxLogFileEntries or
         --#      UsedLogFiles.Length < LogFileCountT'Last);
      pragma Assert_And_Cut
        (NumberLogEntries =
           LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
           LogFileEntries(CurrentLogFile) and then
           (LogFileEntries(CurrentLogFile) < MaxLogFileEntries or else
            UsedLogFiles.Length < LogFileCountT'Last));

      AddElementToLogFile
        ( ElementID   => ElementID,
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
   --# global in     ConfigData.State;
   --#        in out LogFiles;
   --#           out AuditAlarm;
   --#           out NumberLogEntries;
   --#           out AuditSystemFault;
   --#           out LogFilesStatus;
   --#           out LogFileEntries;
   --#           out CurrentLogFile;
   --#           out UsedLogFiles;
   --# derives NumberLogEntries,
   --#         AuditSystemFault,
   --#         LogFiles,
   --#         LogFilesStatus,
   --#         LogFileEntries,
   --#         CurrentLogFile,
   --#         UsedLogFiles     from LogFiles &
   --#         AuditAlarm       from ConfigData.State,
   --#                               LogFiles;
   --# post NumberLogEntries = LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
   --#                        LogFileEntries(CurrentLogFile);
   is
     type FileAgeT is array (LogFileIndexT) of Clock.TimeTextT;
     FileAges      : FileAgeT;
     OK            : Boolean;

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
       --# global in out AuditSystemFault;
       --#        in out LogFiles;
       --#           out LogFilesStatus;
       --#           out LogFileEntries;
       --#           out FileAges;
       --# derives AuditSystemFault,
       --#         LogFiles         from *,
       --#                               LogFiles &
       --#         LogFilesStatus,
       --#         LogFileEntries,
       --#         FileAges         from LogFiles;

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
        procedure GetFileDetails ( I : in LogFileIndexT)
          --# global in     LogFiles;
          --#        in out AuditSystemFault;
          --#           out FirstTime;
          --#           out Status;
          --#           out NumberEntries;
          --#           out FileH;
          --# derives FirstTime,
          --#         Status,
          --#         NumberEntries,
          --#         FileH            from LogFiles,
          --#                               I &
          --#         AuditSystemFault from *,
          --#                               LogFiles,
          --#                               I;
        is
           OK : Boolean;
           TimeOK : Boolean := True;
           TimeCount : Natural;
        begin
           -- Try to  open the file
           NumberEntries := 0;
           FirstTime := Clock.PrintTime(Clock.ZeroTime);
           FileH := LogFiles(I);
           File.SetName (TheName => LogFileNames(I),
                         TheFile => FileH);

           if File.Exists( TheFile => FileH) then
              File.OpenRead( TheFile => FileH,
                             Success => OK );
              if OK then
                 -- if can open then see if it is empty
                 if File.EndOfFile(FileH) then
                    Status := Free;
                 else
                    Status := Used;
                    -- get the age of the first element
                    File.GetString( TheFile => FileH,
                                    Text    => FirstTime,
                                    Stop    => TimeCount);
                    if TimeCount /= FirstTime'Last then
                       -- Time was corrupt
                       TimeOK := False;
                    end if;
                    -- See how full it is
                    while not File.EndOfFile(FileH) loop
                       --# assert NumberEntries >= 0 and
                       --#        NumberEntries < MaxLogFileEntries;
                        pragma Loop_Invariant
                          (NumberEntries >= 0 and then
                           NumberEntries < MaxLogFileEntries);
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

        --# accept F, 23, LogFilesStatus, "Array initialization is total in loop" &
        --#        F, 23, LogFileEntries, "Array initialization is total in loop" &
        --#        F, 23, FileAges,       "Array initialization is total in loop";
        for I in LogFileIndexT loop
           --# assert I in LogFileIndexT;
           pragma Loop_Invariant (I in LogFileIndexT);
           GetFileDetails(I);
           LogFilesStatus(I) := Status;
           LogFiles(I)       := FileH;
           FileAges(I)       := FirstTime;
           LogFileEntries(I) := NumberEntries;
        end loop;

        --# accept F, 602, LogFilesStatus, LogFilesStatus, "Array initialization is total in loop" &
        --#        F, 602, LogFileEntries, LogFileEntries, "Array initialization is total in loop" &
        --#        F, 602, FileAges,       FileAges,       "Array initialization is total in loop";
     end SetFileDetails;

     ------------------------------------------------------------------
     -- AgeLessThan
     --
     --    Description:
     --       Compares two date strings.
     --
     --    Implementation Notes:
     --       Hidden since string comparison not supported by VCG.
     --
     ------------------------------------------------------------------
     function AgeLessThan (Left, Right : Clock.TimeTextT) return Boolean
     is
        --# hide AgeLessThan;
     begin
        return Left < Right;
     end AgeLessThan;

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
         --# assert I in LogFileIndexT and
         --#        UsedLogFiles.Length in LogFileCountT and
         --#        UsedLogFiles.Length < I and
         --#        UsedLogFiles.LastI in LogFileIndexT and
         --#        (UsedLogFiles.Length > 0 -> UsedLogFiles.LastI < I) and
         --#        (for all N in LogFileIndexT =>
         --#             (LogFileEntries(N) in FileEntryCountT))  and
         --#        (for all N in LogFileIndexT =>
         --#             (UsedLogFiles.List(N) in LogFileIndexT)) ;
         pragma Loop_Invariant
           (I in LogFileIndexT and then
            UsedLogFiles.Length in LogFileCountT and then
            UsedLogFiles.Length < I and then
            UsedLogFiles.LastI in LogFileIndexT and then
              ((UsedLogFiles.Length > 0) <= (UsedLogFiles.LastI < I))) ;
         if LogFilesStatus(I) = Used then
            if UsedLogFiles.Length = 0 then
               -- easy case list currently empty
               UsedLogFiles.Head := LogFileIndexT'First;
               UsedLogFiles.LastI := LogFileIndexT'First;
               UsedLogFiles.Length := 1;
               UsedLogFiles.List(UsedLogFiles.Head) := I;
            else
               for J in LogFileIndexT  range 1 .. UsedLogFiles.LastI loop
                  --# assert I in LogFileIndexT and
                  --#        J in LogFileIndexT and
                  --#        J <= UsedLogFiles.LastI and
                  --#        UsedLogFiles.LastI in LogFileIndexT and
                  --#        UsedLogFiles.Length in LogFileCountT and
                  --#        UsedLogFiles.Length > 0 and
                  --#        UsedLogFiles.Length < I and
                  --#        (UsedLogFiles.Length > 0 -> UsedLogFiles.LastI < I) and
                  --#        (for all N in LogFileIndexT =>
                  --#             (LogFileEntries(N) in FileEntryCountT)) and
                  --#        (for all N in LogFileIndexT =>
                  --#             (UsedLogFiles.List(N) in LogFileIndexT)) ;
                  pragma Loop_Invariant
                    (I in LogFileIndexT and then
                     J in LogFileIndexT and then
                     J <= UsedLogFiles.LastI and then
                     UsedLogFiles.LastI in LogFileIndexT and then
                     UsedLogFiles.Length in LogFileCountT and then
                     UsedLogFiles.Length > 0 and then
                     UsedLogFiles.Length < I and then
                       ((UsedLogFiles.Length > 0) <= (UsedLogFiles.LastI < I))) ;
                  if AgeLessThan( FileAges(I), FileAges( UsedLogFiles.List(J))) then
                     -- this is where the new entry goes.
                     -- move all other entries up the list to make room
                     UsedLogFiles.LastI := UsedLogFiles.LastI + 1;
                     UsedLogFiles.Length := UsedLogFiles.Length + 1;
                     for K in reverse LogFileIndexT
                       range J + 1 .. UsedLogFiles.LastI loop
                        --# assert K in LogFileIndexT and
                        --#        J in LogFileIndexT and
                        --#        I in LogFileIndexT and
                        --#        J = J% and
                        --#        K >= J + 1 and K <= UsedLogFiles.LastI and
                        --#        UsedLogFiles.LastI in LogFileIndexT and
                        --#        UsedLogFiles.Length in LogFileCountT and
                        --#        UsedLogFiles.Length > 0 and
                        --#        UsedLogFiles.Length <= I and
                        --#        UsedLogFiles.LastI <= I and
                        --#        (for all N in LogFileIndexT =>
                        --#             (LogFileEntries(N) in FileEntryCountT)) and
                        --#        (for all N in LogFileIndexT =>
                        --#             (UsedLogFiles.List(N) in LogFileIndexT)) ;
                        pragma Loop_Invariant
                          (K in LogFileIndexT and then
                           J in LogFileIndexT and then
                           I in LogFileIndexT and then
                           K >= J + 1 and then
                           K <= UsedLogFiles.LastI and then
                           UsedLogFiles.LastI in LogFileIndexT and then
                           UsedLogFiles.Length in LogFileCountT and then
                           UsedLogFiles.Length > 0 and then
                           UsedLogFiles.Length <= I and then
                           UsedLogFiles.LastI <= I) ;
                        UsedLogFiles.List(K) := UsedLogFiles.List(K - 1);
                     end loop;
                     UsedLogFiles.List(J) := I;
                     exit;
                  end if;
                  if J = UsedLogFiles.LastI then
                     -- entry goes at the end
                     UsedLogFiles.LastI := UsedLogFiles.LastI + 1;
                     UsedLogFiles.Length := UsedLogFiles.Length + 1;
                     UsedLogFiles.List(UsedLogFiles.LastI) := I;
                     exit;
                  end if;
               end loop;
            end if;
         end if;
      end loop;

      --# assert UsedLogFiles.Length in LogFileCountT and
      --#        UsedLogFiles.LastI in LogFileIndexT and
      --#        (for all N in LogFileIndexT =>
      --#             (LogFileEntries(N) in FileEntryCountT))  and
      --#        (for all N in LogFileIndexT =>
      --#             (UsedLogFiles.List(N) in LogFileIndexT)) ;
      pragma Assert_And_Cut
        (UsedLogFiles.Length in LogFileCountT and then
         UsedLogFiles.LastI in LogFileIndexT and then
         (for all N in LogFileIndexT =>
           (LogFileEntries(N) in FileEntryCountT)) and then
         (for all N in LogFileIndexT =>
           (UsedLogFiles.List(N) in LogFileIndexT)));
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

      --# assert UsedLogFiles.Length in LogFileCountT and
      --#        UsedLogFiles.Length > 0 and
      --#        (LogFileEntries(CurrentLogFile) in FileEntryCountT) and
      --#        CurrentLogFile in LogFileIndexT;
      pragma Assert_And_Cut
        (UsedLogFiles.Length in LogFileCountT and then
         UsedLogFiles.Length > 0 and then
           (LogFileEntries(CurrentLogFile) in FileEntryCountT) and then
         CurrentLogFile in LogFileIndexT);

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
                ElementID    : in     AuditTypes.ElementT;
                Severity     : in     AuditTypes.SeverityT;
                User         : in     AuditTypes.UserTextT;
                Description  : in     String)
     --# global in     ConfigData.State;
     --#        in     Clock.Now;
     --#        in out AuditAlarm;
     --#        in out NumberLogEntries;
     --#        in out AuditSystemFault;
     --#        in out LogFiles;
     --#        in out LogFilesStatus;
     --#        in out LogFileEntries;
     --#        in out CurrentLogFile;
     --#        in out UsedLogFiles;
     --# derives AuditAlarm,
     --#         NumberLogEntries,
     --#         LogFilesStatus,
     --#         LogFileEntries,
     --#         CurrentLogFile,
     --#         UsedLogFiles     from AuditAlarm,
     --#                               NumberLogEntries,
     --#                               ConfigData.State,
     --#                               LogFilesStatus,
     --#                               LogFileEntries,
     --#                               CurrentLogFile,
     --#                               UsedLogFiles &
     --#         AuditSystemFault,
     --#         LogFiles         from *,
     --#                               AuditAlarm,
     --#                               NumberLogEntries,
     --#                               ConfigData.State,
     --#                               Description,
     --#                               LogFiles,
     --#                               LogFilesStatus,
     --#                               LogFileEntries,
     --#                               Clock.Now,
     --#                               ElementID,
     --#                               Severity,
     --#                               User,
     --#                               CurrentLogFile,
     --#                               UsedLogFiles;
     --# pre NumberLogEntries =
     --#     LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
     --#     LogFileEntries(CurrentLogFile);
     --# post NumberLogEntries =
     --#     LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
     --#     LogFileEntries(CurrentLogFile);
   is
      OldAlarm : AlarmTypes.StatusT;

   begin

      OldAlarm := AuditAlarm;

      AddElementToLogFileWithTruncateChecks
        (ElementID    => ElementID,
         Severity     => Severity,
         User         => User,
         Description  => ConvertToAuditDescription(Description));

      CheckLogAlarm;

      if OldAlarm /= AuditAlarm then
         -- This will always raise alarms not clear them
         AddElementToLogFileWithTruncateChecks
           (ElementID    => AuditTypes.AuditAlarmRaised,
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
     --# global in     ConfigData.State;
     --#        in     Clock.Now;
     --#        in out AuditAlarm;
     --#        in out NumberLogEntries;
     --#        in out AuditSystemFault;
     --#        in out LogFiles;
     --#        in out LogFilesStatus;
     --#        in out LogFileEntries;
     --#        in out CurrentLogFile;
     --#        in out UsedLogFiles;
     --# derives AuditAlarm,
     --#         NumberLogEntries,
     --#         LogFilesStatus,
     --#         LogFileEntries,
     --#         CurrentLogFile,
     --#         UsedLogFiles     from AuditAlarm,
     --#                               NumberLogEntries,
     --#                               ConfigData.State,
     --#                               LogFiles,
     --#                               LogFilesStatus,
     --#                               LogFileEntries,
     --#                               CurrentLogFile,
     --#                               UsedLogFiles &
     --#         AuditSystemFault,
     --#         LogFiles         from *,
     --#                               AuditAlarm,
     --#                               NumberLogEntries,
     --#                               ConfigData.State,
     --#                               LogFiles,
     --#                               LogFilesStatus,
     --#                               LogFileEntries,
     --#                               Clock.Now,
     --#                               User,
     --#                               CurrentLogFile,
     --#                               UsedLogFiles &
     --#         Archive          from LogFiles,
     --#                               LogFileEntries,
     --#                               UsedLogFiles;
     --# pre NumberLogEntries =
     --#     LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
     --#     LogFileEntries(CurrentLogFile);
     --# post NumberLogEntries =
     --#     LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
     --#     LogFileEntries(CurrentLogFile);

   is
      Description : AuditTypes.DescriptionT;
      TheFile : File.T;
      OK : Boolean;
      ArchiveFault : Boolean := False;
      ArchivedFileCount : LogFileCountT;
      FileIndex : LogFileIndexT;
      FileIndexInUsedList : LogFileIndexT;
   begin

      Archive := File.Construct (TheName => ArchiveFileName);

      Description := ConvertToAuditDescription("Nothing archived");

      if UsedLogFiles.Length = 0 or
        (UsedLogFiles.Length = 1
        and LogFileEntries(UsedLogFiles.List(UsedLogFiles.Head))
               < MaxLogFileEntries) then
         -- Make an empty file to return

         File.OpenWrite( TheFile => Archive,
                         Success => OK );

         --# accept F, 22, "Invariant expression expected and OK here";
         if not OK then
            File.Create( TheFile => Archive,
                         Success => OK);
         end if;
         --# end accept;

         ArchiveFault := not OK;

         File.Close( TheFile => Archive,
                     Success => OK);

         ArchiveFault := ArchiveFault or not OK;

      else
         ArchivedFileCount := 0;
         FileIndexInUsedList := UsedLogFiles.Head;

         while ArchivedFileCount < MaxNumberArchivableFiles
            and ArchivedFileCount < UsedLogFiles.Length loop
            --# assert FileIndexInUsedList in LogFileIndexT and
            --#   ArchivedFileCount >= 0 and
            --#   ArchivedFileCount < MaxNumberArchivableFiles and
            --#   NumberLogEntries =
            --#     LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
            --#     LogFileEntries(CurrentLogFile);
            pragma Loop_Invariant
              (FileIndexInUsedList in LogFileIndexT and then
               ArchivedFileCount >= 0 and then
               ArchivedFileCount < MaxNumberArchivableFiles and then
               NumberLogEntries =
                 LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
                 LogFileEntries(CurrentLogFile));

            FileIndex := UsedLogFiles.List(FileIndexInUsedList);
            exit when LogFileEntries( FileIndex) < MaxLogFileEntries;

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
                 ( TheFile     => TheFile,
                   Description => Description);
            else
               UpdateEndTimeFromFile
                 ( TheFile     => TheFile,
                   Description => Description);
            end if;

            LogFiles (FileIndex) := TheFile;
            ArchivedFileCount := ArchivedFileCount + 1;
            FileIndexInUsedList := NextListIndex ( FileIndexInUsedList);

         end loop;

      end if;

      --# assert NumberLogEntries =
      --#     LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
      --#     LogFileEntries(CurrentLogFile);
      pragma Assert_And_Cut
        (NumberLogEntries =
           LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
           LogFileEntries(CurrentLogFile));

      if ArchiveFault then
         AddElementToLog
           ( ElementID   => AuditTypes.SystemFault,
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
   procedure ClearLogEntries (User    : in     AuditTypes.UserTextT)
     --# global in     ConfigData.State;
     --#        in     Clock.Now;
     --#        in out AuditAlarm;
     --#        in out NumberLogEntries;
     --#        in out AuditSystemFault;
     --#        in out LogFiles;
     --#        in out LogFilesStatus;
     --#        in out LogFileEntries;
     --#        in out CurrentLogFile;
     --#        in out UsedLogFiles;
     --# derives AuditAlarm,
     --#         NumberLogEntries,
     --#         LogFilesStatus,
     --#         LogFileEntries,
     --#         CurrentLogFile,
     --#         UsedLogFiles     from AuditAlarm,
     --#                               NumberLogEntries,
     --#                               ConfigData.State,
     --#                               LogFilesStatus,
     --#                               LogFileEntries,
     --#                               CurrentLogFile,
     --#                               UsedLogFiles &
     --#         AuditSystemFault,
     --#         LogFiles         from *,
     --#                               AuditAlarm,
     --#                               NumberLogEntries,
     --#                               ConfigData.State,
     --#                               LogFiles,
     --#                               LogFilesStatus,
     --#                               LogFileEntries,
     --#                               Clock.Now,
     --#                               User,
     --#                               CurrentLogFile,
     --#                               UsedLogFiles;
     --# pre NumberLogEntries = LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
     --#                        LogFileEntries(CurrentLogFile);
     --# post NumberLogEntries = LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
     --#                        LogFileEntries(CurrentLogFile);
   is
      OldAlarm : AlarmTypes.StatusT;

   begin


      -- Note the CurrentLogFile cannot be Archived.

      while UsedLogFiles.Length > 1 loop
         --# assert UsedLogFiles.Length > 1 and
         --#       NumberLogEntries =
         --#          LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
         --#                        LogFileEntries(CurrentLogFile);
         pragma Loop_Invariant
           (UsedLogFiles.Length > 1 and then
            NumberLogEntries =
              LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
              LogFileEntries(CurrentLogFile));
         exit when LogFilesStatus(UsedLogFiles.List(UsedLogFiles.Head))
           /= Archived;
         --# assert UsedLogFiles.Length > 1 and
         --#        LogFilesStatus(UsedLogFiles.List(UsedLogFiles.Head))
         --#                = Archived and
         --#       NumberLogEntries =
         --#          LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
         --#                        LogFileEntries(CurrentLogFile);
         pragma Loop_Invariant
           (UsedLogFiles.Length > 1 and then
            LogFilesStatus(UsedLogFiles.List(UsedLogFiles.Head))
            = Archived and then
            NumberLogEntries =
              LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
              LogFileEntries(CurrentLogFile));

         -- Empty the archived file.
         DeleteLogFile (UsedLogFiles.List(UsedLogFiles.Head));

         UsedLogFiles.Length := UsedLogFiles.Length - 1;
         UsedLogFiles.Head := NextListIndex (UsedLogFiles.Head);

         NumberLogEntries := NumberLogEntries - MaxLogFileEntries;

      end loop;

      --# assert NumberLogEntries =
      --#          LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
      --#                        LogFileEntries(CurrentLogFile);
      pragma Assert_And_Cut
        (NumberLogEntries =
           LogEntryCountT(UsedLogFiles.Length -1)*MaxLogFileEntries +
           LogFileEntries(CurrentLogFile));
      OldAlarm := AuditAlarm;

      AuditAlarm := AlarmTypes.Silent;
      CheckLogAlarm;

      if OldAlarm /= AuditAlarm then
         -- Archiving will always clear alarms not raise them.
         -- Note that adding this entry could result in the alarm
         -- being raised again (this will be handled by AddElementToLog).
         AddElementToLog
           (ElementID    => AuditTypes.AuditAlarmSilenced,
            Severity     => AuditTypes.Information,
            User         => AuditTypes.NoUser,
            Description  => AuditTypes.NoDescription);

      end if;

      AddElementToLog
        (ElementID   => AuditTypes.ArchiveComplete,
         Severity    => AuditTypes.Information,
         User        => User,
         Description => AuditTypes.NoDescription);

      DeleteArchiveFile;

   end ClearLogEntries;


   ------------------------------------------------------------------
   -- CancelArchive
   --
   --   Implementation Notes:
   --      This does not add log entries.
   ------------------------------------------------------------------

   procedure CancelArchive
   --# global in out LogFilesStatus;
   --# derives LogFilesStatus from *;
   is
   begin
      for I in LogFileIndexT loop
         --# assert I in LogFileIndexT ;
         pragma Loop_Invariant (I in LogFileIndexT);
         if LogFilesStatus(I) = Archived then
            LogFilesStatus(I) := Used;
         end if;
      end loop;

      DeleteArchiveFile;

   end CancelArchive;

   ------------------------------------------------------------------
   -- TheAuditAlarm
   --
   --   Implementation Notes:
   --      None
   ------------------------------------------------------------------

   function TheAuditAlarm return AlarmTypes.StatusT
   --# global AuditAlarm;
   is
   begin
      return AuditAlarm;
   end TheAuditAlarm;

   ------------------------------------------------------------------
   -- SystemFaultOccurred
   --
   --   Implementation Notes:
   --      None
   ------------------------------------------------------------------

   function SystemFaultOccurred return Boolean
   --# global AuditSystemFault;
   is
   begin
      return AuditSystemFault;
   end SystemFaultOccurred;


end AuditLog;
