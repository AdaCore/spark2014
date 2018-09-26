
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
-- ConfigData
--
-- Description:
--    Package that maintains the system configuration data.
--
------------------------------------------------------------------

with AuditTypes,
     Clock,
     CommonTypes,
     File,
     IandATypes,
     PrivTypes;

package ConfigData
  with Abstract_State => (FileState,
                          State),
       Initializes    => Filestate
is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   subtype DurationT is Clock.DurationT range 0..2000;

   function DurationT_Image (X : DurationT) return CommonTypes.StringF1L3to1000 is
      (DurationT'Image (X));
   pragma Annotate (GNATprove, False_Positive,
                    "predicate check might fail",
                    "Image of integers of type Unsigned32T are non-empty short strings starting at index 1");


   type AccessPolicyT is (WorkingHours, AllHours);

   function AccessPolicyT_Image (X : AccessPolicyT) return CommonTypes.StringF1L12 is
      (AccessPolicyT'Image (X));
   pragma Annotate (GNATprove, False_Positive,
                    "predicate check might fail",
                    "Image of enums of type AccessPolicyT are short strings starting at index 1");

   ------------------------------------------------------------------
   -- Init
   --
   -- Description:
   --      Initialises the configuration data.Takes the data from file
   --      if it can.
   --
   -- Traceunit: C.ConfigData.Init
   -- Traceto: FD.TIS.TISStartup
   -- Traceto: FD.TIS.InitIDStation
   ------------------------------------------------------------------
   procedure Init
     with Global  => (Output => State,
                      In_Out => FileState),
          Depends => ((FileState,
                       State)     => FileState);

   ------------------------------------------------------------------
   -- UpdateData
   --
   -- Description:
   --      Updates the configuration data.
   --      DOES NOT RAISE AUDIT ENTRIES.
   --
   -- Traceunit: C.ConfigData.UpdateData
   -- Traceto: FD.Enclave.FinishUpdateConfigDataOK
   ------------------------------------------------------------------
   procedure UpdateData
     (TheLatchUnlockDuration  : in     DurationT;
      TheAlarmSilentDuration  : in     DurationT;
      TheFingerWaitDuration   : in     DurationT;
      TheTokenRemovalDuration : in     DurationT;
      TheEnclaveClearance     : in     PrivTypes.ClassT;
      TheWorkingHoursStart    : in     Clock.DurationT;
      TheWorkingHoursEnd      : in     Clock.DurationT;
      TheMaxAuthDuration      : in     Clock.DurationT;
      TheAccessPolicy         : in     AccessPolicyT;
      TheMinEntryClass        : in     PrivTypes.ClassT;
      TheMinPreservedLogSize  : in     AuditTypes.FileSizeT;
      TheAlarmThresholdSize   : in     AuditTypes.FileSizeT;
      TheSystemMaxFar         : in     IandATypes.FarT
      )
     with Global  => (Output => State),
          Depends => (State => (TheAccessPolicy,
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
                                TheWorkingHoursStart));

   ------------------------------------------------------------------
   -- WriteFile
   --
   -- Description:
   --      Writes the supplied configuration values to file.
   --      Success is True only if the file is written OK.
   --
   -- Traceunit: C.ConfigData.WriteFile
   -- Traceto: FD.Enclave.FinishUpdateConfigDataOK
   ------------------------------------------------------------------
   procedure WriteFile
     (Success                 :    out Boolean;
      TheLatchUnlockDuration  : in     DurationT;
      TheAlarmSilentDuration  : in     DurationT;
      TheFingerWaitDuration   : in     DurationT;
      TheTokenRemovalDuration : in     DurationT;
      TheEnclaveClearance     : in     PrivTypes.ClassT;
      TheWorkingHoursStart    : in     Clock.DurationT;
      TheWorkingHoursEnd      : in     Clock.DurationT;
      TheMaxAuthDuration      : in     Clock.DurationT;
      TheAccessPolicy         : in     AccessPolicyT;
      TheMinEntryClass        : in     PrivTypes.ClassT;
      TheMinPreservedLogSize  : in     AuditTypes.FileSizeT;
      TheAlarmThresholdSize   : in     AuditTypes.FileSizeT;
      TheSystemMaxFar         : in     IandATypes.FarT
      )
     with Global  => (In_Out => FileState),
          Depends => ((FileState,
                       Success)   => (FileState,
                                      TheAccessPolicy,
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
                                      TheWorkingHoursStart));

   ------------------------------------------------------------------
   -- TheDisplayFields
   --
   -- Description:
   --      Retrieves the fields that may be presented in the display.
   --
   -- Traceunit: C.ConfigData.TheDisplayFields
   -- Traceto: FD.TIS.State
   ------------------------------------------------------------------
   procedure TheDisplayFields
     (TheLatchUnlockDuration  : out DurationT;
      TheAlarmSilentDuration  : out DurationT;
      TheFingerWaitDuration   : out DurationT;
      TheTokenRemovalDuration : out DurationT;
      TheEnclaveClearance     : out PrivTypes.ClassT;
      TheWorkingHoursStart    : out Clock.DurationT;
      TheWorkingHoursEnd      : out Clock.DurationT;
      TheMaxAuthDuration      : out Clock.DurationT;
      TheAccessPolicy         : out AccessPolicyT;
      TheMinEntryClass        : out PrivTypes.ClassT;
      TheMinPreservedLogSize  : out AuditTypes.FileSizeT;
      TheAlarmThresholdSize   : out AuditTypes.FileSizeT;
      TheSystemMaxFar         : out IandATypes.FarT
      )
     with Global  => State,
          Depends => ((TheAccessPolicy,
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
                       TheWorkingHoursStart)    => State);

   ------------------------------------------------------------------
   -- ValidateFile
   --
   -- Description:
   --      Validates the contents of a configuration file and returns
   --      the configuration data if validation is successful.
   --
   -- Traceunit: C.ConfigData.ValidateFile
   -- Traceto: FD.ConfigData.State
   ------------------------------------------------------------------
   procedure ValidateFile
     (TheFile                 : in out File.T;
      Success                 :    out Boolean;
      TheLatchUnlockDuration  :    out DurationT;
      TheAlarmSilentDuration  :    out DurationT;
      TheFingerWaitDuration   :    out DurationT;
      TheTokenRemovalDuration :    out DurationT;
      TheEnclaveClearance     :    out PrivTypes.ClassT;
      TheWorkingHoursStart    :    out Clock.DurationT;
      TheWorkingHoursEnd      :    out Clock.DurationT;
      TheMaxAuthDuration      :    out Clock.DurationT;
      TheAccessPolicy         :    out AccessPolicyT;
      TheMinEntryClass        :    out PrivTypes.ClassT;
      TheMinPreservedLogSize  :    out AuditTypes.FileSizeT;
      TheAlarmThresholdSize   :    out AuditTypes.FileSizeT;
      TheSystemMaxFar         :    out IandATypes.FarT
      )
     with Global  => null,
          Depends => ((Success,
                       TheAccessPolicy,
                       TheAlarmSilentDuration,
                       TheAlarmThresholdSize,
                       TheEnclaveClearance,
                       TheFile,
                       TheFingerWaitDuration,
                       TheLatchUnlockDuration,
                       TheMaxAuthDuration,
                       TheMinEntryClass,
                       TheMinPreservedLogSize,
                       TheSystemMaxFar,
                       TheTokenRemovalDuration,
                       TheWorkingHoursEnd,
                       TheWorkingHoursStart) => TheFile);

   ------------------------------------------------------------------
   -- AuthPeriodIsEmpty
   --
   -- Description:
   --      Returns true if the Auth Period is empty.
   --
   -- Traceunit : C.ConfigData.AuthPeriodIsEmpty
   -- Traceto : FD.CongfigData.State
   ------------------------------------------------------------------
   function AuthPeriodIsEmpty return Boolean
     with Global => State;

   ------------------------------------------------------------------
   -- GetAuthPeriod
   --
   -- Description:
   --      Returns the start and end of the Auth Period.
   --
   -- Traceunit : C.ConfigData.GetAuthPeriod
   -- Traceto : FD.CongfigData.State
   ------------------------------------------------------------------
   procedure GetAuthPeriod
     (TheTime   : in     Clock.TimeT;
       NotBefore :    out Clock.TimeT;
       NotAfter  :    out Clock.TimeT)
     with Global  => State,
          Depends => ((NotAfter,
                       NotBefore) => (State,
                                      TheTime));

   ------------------------------------------------------------------
   -- IsInEntryPeriod
   --
   -- Description:
   --      Returns true if the supplied time is in a valid
   --      entry period for a user with the given CLASS.
   --
   -- Traceunit : C.ConfigData.IsInEntryPeriod
   -- Traceto : FD.CongfigData.State
   ------------------------------------------------------------------
   function IsInEntryPeriod
     (Class   : PrivTypes.ClassT;
       TheTime : Clock.TimeT) return Boolean
     with Global => State;

   ------------------------------------------------------------------
   -- TheLatchUnlockDuration
   --
   -- Description:
   --      Retrieves the latchUnlockDuration.
   --
   -- Traceunit : C.ConfigData.TheLatchUnlockDuration
   -- Traceto : FD.CongfigData.State
   ------------------------------------------------------------------
   function TheLatchUnlockDuration return DurationT
     with Global => State;

   ------------------------------------------------------------------
   -- TheAlarmSilentDuration
   --
   -- Description:
   --      Retrieves the alarmSilentDuration.
   --
   -- Traceunit : C.ConfigData.TheAlarmSilentDuration
   -- Traceto : FD.CongfigData.State
   ------------------------------------------------------------------
   function TheAlarmSilentDuration return DurationT
     with Global => State;

   ------------------------------------------------------------------
   -- TheFingerWaitDuration
   --
   -- Description:
   --      Retrieves the fingerWaitDuration.
   --
   -- Traceunit : C.ConfigData.TheFingerWaitDuration
   -- Traceto : FD.CongfigData.State
   ------------------------------------------------------------------
   function TheFingerWaitDuration return DurationT
     with Global => State;

   ------------------------------------------------------------------
   -- TheTokenRemovalDuration
   --
   -- Description:
   --      Retrieves the tokenRemovalDuration.
   --
   -- Traceunit : C.ConfigData.TheTokenRemovalDuration
   -- Traceto : FD.CongfigData.State
   ------------------------------------------------------------------
   function TheTokenRemovalDuration return DurationT
     with Global => State;

   ------------------------------------------------------------------
   -- TheEnclaveClearance
   --
   -- Description:
   --      Retrieves the enclaveClearance.
   --
   -- Traceunit : C.ConfigData.TheEnclaveClearance
   -- Traceto : FD.CongfigData.State
   ------------------------------------------------------------------
   function TheEnclaveClearance return PrivTypes.ClassT
     with Global => State;

   ------------------------------------------------------------------
   -- TheSystemMaxFar
   --
   -- Description:
   --      Retrieves the systemMaxFar.
   --
   -- Traceunit : C.ConfigData.TheSystemMaxFar
   -- Traceto : FD.CongfigData.State
   ------------------------------------------------------------------
   function TheSystemMaxFar return IandATypes.FarT
     with Global => State;

   ------------------------------------------------------------------
   -- TheAlarmThresholdEntries
   --
   -- Description:
   --      Retrieves the alarmThresholdEntries.
   --
   -- Traceunit : C.ConfigData.TheAlarmThresholdEntries
   -- Traceto : FD.CongfigData.State
   ------------------------------------------------------------------
   function TheAlarmThresholdEntries return AuditTypes.AuditEntryCountT
     with Global => State;

end ConfigData;
