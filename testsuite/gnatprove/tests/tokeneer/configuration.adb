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

with AuditTypes,
     Clock;

use type Clock.DurationT;
use type AuditTypes.FileSizeT;

package body Configuration is

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
     (TheFile   : in out File.T;
      DataValid :    out Boolean)
   is
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
        with Global => (TheAccessPolicy,
                        TheAlarmSilentDuration,
                        TheAlarmThresholdSize,
                        TheEnclaveClearance,
                        TheFingerWaitDuration,
                        TheLatchUnlockDuration,
                        TheMaxAuthDuration,
                        TheMinEntryClass,
                        TheMinPreservedLogSize,
                        TheSystemMaxFar,
                        TheTokenRemovalDuration,
                        TheWorkingHoursEnd,
                        TheWorkingHoursStart)
      is

         LocalText : AuditTypes.DescriptionT := AuditTypes.NoDescription;
         Str       : String :=
           Clock.DurationT_Image(TheAlarmSilentDuration / 10) & "; "
           & Clock.DurationT_Image(TheLatchUnlockDuration / 10) & "; "
           & Clock.DurationT_Image(TheTokenRemovalDuration / 10) & "; "
           & Clock.DurationT_Image(TheFingerWaitDuration / 10) & "; "
           & PrivTypes.ClassT_Image(TheEnclaveClearance) & "; "
           & Clock.PrintDuration(TheWorkingHoursStart)(1 .. 5) & "; "
           & Clock.PrintDuration(TheWorkingHoursEnd)(1 .. 5) & "; "
           & Clock.PrintDuration(TheMaxAuthDuration)(1 .. 5) & "; "
           & ConfigData.AccessPolicyT_Image(TheAccessPolicy) & "; "
           & PrivTypes.ClassT_Image(TheMinEntryClass) & "; "
           & AuditTypes.FileSizeT_Image(TheMinPreservedLogSize / 1024) & "; "
           & AuditTypes.FileSizeT_Image(TheAlarmThresholdSize / 1024) & "; "
           & IandATypes.FarT_Image(TheSystemMaxFar);

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
         TheSystemMaxFar         => TheSystemMaxFar);

      if DataValid then

         ConfigData.UpdateData
           (TheLatchUnlockDuration  => TheLatchUnlockDuration,
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
            TheSystemMaxFar         => TheSystemMaxFar);

         AuditLog.AddElementToLog
           (ElementID   => AuditTypes.UpdatedConfigData,
            Severity    => AuditTypes.Information,
            User        => AdminToken.ExtractUser,
            Description => MakeDescription);

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
            TheSystemMaxFar         => TheSystemMaxFar);

         if not Success then
            -- Warn that config data will not be preserved through powerdown.
            AuditLog.AddElementToLog
              (ElementID   => AuditTypes.SystemFault,
               Severity    => AuditTypes.Warning,
               User        => AuditTypes.NoUser,
               Description => "Error Writing New Config Data to file");
         end if;

      else
         AuditLog.AddElementToLog
           (ElementID   => AuditTypes.InvalidConfigData,
            Severity    => AuditTypes.Warning,
            User        => AdminToken.ExtractUser,
            Description => AuditTypes.NoDescription);
      end if;

   end UpdateData;

end Configuration;
