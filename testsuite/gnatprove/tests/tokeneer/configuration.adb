



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
-- Implementation Notes:
--    None.
--
------------------------------------------------------------------

with ConfigData;
with PrivTypes;
with AuditTypes;
with AuditLog;
with Clock;
with IandATypes;
with AdminToken;

use type Clock.DurationT;
use type AuditTypes.FileSizeT;

package body Configuration
is pragma SPARK_Mode (On);

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   ------------------------------------------------------------------
   -- Init
   --
   -- Implementation Notes:
   --      None.
   ------------------------------------------------------------------
   procedure Init
   is
   begin
      ConfigData.Init;
   end Init;

   ------------------------------------------------------------------
   -- UpdateData
   --
   -- Implementation Notes:
   --      This follows the Design faithfully, note that this means that
   --      failure to write the Config File does not prevent a change in
   --      the config data.
   --
   ------------------------------------------------------------------
   procedure UpdateData
     (TheFile        : in out File.T;
      DataValid      :    out Boolean)
   is
      pragma SPARK_Mode (Off);  --  concatenation
      TheLatchUnlockDuration  : ConfigData.DurationT;
      TheAlarmSilentDuration  : ConfigData.DurationT;
      TheFingerWaitDuration   : ConfigData.DurationT;
      TheTokenRemovalDuration : ConfigData.DurationT;
      TheEnclaveClearance     : PrivTypes.ClassT;
      TheWorkingHoursStart    : Clock.DurationT;
      TheWorkingHoursEnd      : Clock.DurationT;
      TheMaxAuthDuration      : Clock.DurationT;
      TheAccessPolicy         : ConfigData.AccessPolicyT;
      TheMinEntryClass        : PrivTypes.ClassT;
      TheMinPreservedLogSize  : AuditTypes.FileSizeT;
      TheAlarmThresholdSize   : AuditTypes.FileSizeT;
      TheSystemMaxFar         : IandATypes.FarT;
      Success                 : Boolean;

      ------------------------------------------------------------------
      -- MakeDesciption
      --
      -- Description:
      --      Makes a description text containing new config parameters
      --      for inclusion in audit record.
      --
      -- Implementation Notes:
      --      Hidden due to use of 'Image and slicing.
      ------------------------------------------------------------------
      function MakeDescription return AuditTypes.DescriptionT
        --# global
        --# TheLatchUnlockDuration,
        --# TheAlarmSilentDuration,
        --# TheFingerWaitDuration,
        --# TheTokenRemovalDuration,
        --# TheEnclaveClearance,
        --# TheWorkingHoursStart,
        --# TheWorkingHoursEnd,
        --# TheMaxAuthDuration,
        --# TheAccessPolicy,
        --# TheMinEntryClass,
        --# TheMinPreservedLogSize,
        --# TheAlarmThresholdSize,
        --# TheSystemMaxFar;
      is
         --# hide MakeDescription;

         LocalText : AuditTypes.DescriptionT := AuditTypes.NoDescription;
         Str : String :=
           Clock.DurationT'Image(TheAlarmSilentDuration / 10) & "; "
           & Clock.DurationT'Image(TheLatchUnlockDuration / 10) & "; "
           & Clock.DurationT'Image(TheTokenRemovalDuration / 10) & "; "
           & Clock.DurationT'Image(TheFingerWaitDuration / 10) & "; "
           & PrivTypes.ClassT'Image(TheEnclaveClearance) & "; "
           & Clock.PrintDuration(TheWorkingHoursStart)(1 .. 5) & "; "
           & Clock.PrintDuration(TheWorkingHoursEnd)(1 .. 5) & "; "
           & Clock.PrintDuration(TheMaxAuthDuration)(1 .. 5) & "; "
           & ConfigData.AccessPolicyT'Image(TheAccessPolicy) & "; "
           & PrivTypes.ClassT'Image(TheMinEntryClass) & "; "
           & AuditTypes.FileSizeT'Image(TheMinPreservedLogSize / 1024) & "; "
           & AuditTypes.FileSizeT'Image(TheAlarmThresholdSize / 1024) & "; "
           & IandATypes.FarT'Image(TheSystemMaxFar) ;

      begin

         if Str'Last > LocalText'Last then
            LocalText := Str(1 .. LocalText'Last);
         else
            LocalText(1 .. Str'Last) := Str;
         end if;

         return LocalText;

      end MakeDescription;

   begin

      ConfigData.ValidateFile
        (TheFile                 => TheFile,
         Success                 => DataValid,
         TheLatchUnlockDuration  => TheLatchUnlockDuration,
         TheAlarmSilentDuration  => TheAlarmSilentDuration,
         TheFingerWaitDuration   => TheFingerWaitDuration,
         TheTokenRemovalDuration => TheTokenRemovalDuration,
         TheEnclaveClearance     => TheEnclaveClearance,
         TheWorkingHoursStart    => TheWorkingHoursStart,
         TheWorkingHoursEnd      => TheWorkingHoursEnd,
         TheMaxAuthDuration      => TheMaxAuthDuration,
         TheAccessPolicy         => TheAccessPolicy,
         TheMinEntryClass        => TheMinEntryClass,
         TheMinPreservedLogSize  => TheMinPreservedLogSize,
         TheAlarmThresholdSize   => TheAlarmThresholdSize,
         TheSystemMaxFar         => TheSystemMaxFar );

      if DataValid then

         ConfigData.UpdateData
           ( TheLatchUnlockDuration  => TheLatchUnlockDuration,
             TheAlarmSilentDuration  => TheAlarmSilentDuration,
             TheFingerWaitDuration   => TheFingerWaitDuration,
             TheTokenRemovalDuration => TheTokenRemovalDuration,
             TheEnclaveClearance     => TheEnclaveClearance,
             TheWorkingHoursStart    => TheWorkingHoursStart,
             TheWorkingHoursEnd      => TheWorkingHoursEnd,
             TheMaxAuthDuration      => TheMaxAuthDuration,
             TheAccessPolicy         => TheAccessPolicy,
             TheMinEntryClass        => TheMinEntryClass,
             TheMinPreservedLogSize  => TheMinPreservedLogSize,
             TheAlarmThresholdSize   => TheAlarmThresholdSize,
             TheSystemMaxFar         => TheSystemMaxFar );

         AuditLog.AddElementToLog
           ( ElementID   => AuditTypes.UpdatedConfigData,
             Severity    => AuditTypes.Information,
             User        => AdminToken.ExtractUser,
             Description => MakeDescription
             );

         ConfigData.WriteFile
           (Success                 => Success,
            TheLatchUnlockDuration  => TheLatchUnlockDuration,
            TheAlarmSilentDuration  => TheAlarmSilentDuration,
            TheFingerWaitDuration   => TheFingerWaitDuration,
            TheTokenRemovalDuration => TheTokenRemovalDuration,
            TheEnclaveClearance     => TheEnclaveClearance,
            TheWorkingHoursStart    => TheWorkingHoursStart,
            TheWorkingHoursEnd      => TheWorkingHoursEnd,
            TheMaxAuthDuration      => TheMaxAuthDuration,
            TheAccessPolicy         => TheAccessPolicy,
            TheMinEntryClass        => TheMinEntryClass,
            TheMinPreservedLogSize  => TheMinPreservedLogSize,
            TheAlarmThresholdSize   => TheAlarmThresholdSize,
            TheSystemMaxFar         => TheSystemMaxFar );

         if not Success then

            -- Warn that config data will not be preserved through powerdown.

            AuditLog.AddElementToLog
              ( ElementID   => AuditTypes.SystemFault,
                Severity    => AuditTypes.Warning,
                User        => AuditTypes.NoUser,
                Description => "Error Writing New Config Data to file"
                );

         end if;

      else

         AuditLog.AddElementToLog
           ( ElementID   => AuditTypes.InvalidConfigData,
             Severity    => AuditTypes.Warning,
             User        => AdminToken.ExtractUser,
             Description => AuditTypes.NoDescription
             );

      end if;

   end UpdateData;


end Configuration;
