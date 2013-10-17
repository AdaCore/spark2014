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
-- Screen
--
-- Implementatin Notes:
--    None.
--
------------------------------------------------------------------
with Door;
with Clock;
use type Clock.DurationT;
with Stats;
use type Stats.T;

with AuditTypes;
use type AuditTypes.FileSizeT;
with AlarmTypes;
with Screen.Interfac;
with IandATypes;
with PrivTypes;
with ConfigData;
with AuditLog;
use type AlarmTypes.StatusT;

package body Screen
--# own State is TheMsg,
--#              CurrentMsg,
--#              CurrentStats,
--#              CurrentConfig,
--#              CurrentDoorAlarm,
--#              CurrentLogAlarm &
--#
--#     Output is out Screen.Interfac.Output;

is pragma SPARK_Mode (On);

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   subtype MsgStringI is Positive range 1 .. 43;
   subtype MsgStringT is String(MsgStringI);

   type MsgStringLookupT is array (MsgTextT) of MsgStringT;

   type ScreenStatsT is
      record
         IsDisplayed : Boolean;
         Data : Stats.T;
      end record;

   type DisplayedConfigT is
      record
         LatchUnlock     : Clock.DurationT;
         AlarmSilent     : Clock.DurationT;
         FingerWait      : Clock.DurationT;
         TokenRemove     : Clock.DurationT;
         WorkStart       : Clock.DurationT;
         WorkEnd         : Clock.DurationT;
         AuthDuration    : Clock.DurationT;
         Policy          : ConfigData.AccessPolicyT;
         MinPreservedLog : AuditTypes.FileSizeT;
         AlarmThreshold  : AuditTypes.FileSizeT;
         MinEntry        : PrivTypes.ClassT;
         Clearance       : PrivTypes.ClassT;
         MaxFAR          : IandATypes.FarT;
      end record;

   NullConfigData : constant DisplayedConfigT :=
     DisplayedConfigT'(
         LatchUnlock     => Clock.DurationT'First,
         AlarmSilent     => Clock.DurationT'First,
         FingerWait      => Clock.DurationT'First,
         TokenRemove     => Clock.DurationT'First,
         WorkStart       => Clock.DurationT'First,
         WorkEnd         => Clock.DurationT'First,
         AuthDuration    => Clock.DurationT'First,
         Policy          => ConfigData.AccessPolicyT'First,
         MinPreservedLog => AuditTypes.FileSizeT'First,
         AlarmThreshold  => AuditTypes.FileSizeT'First,
         MinEntry        => PrivTypes.ClassT'First,
         Clearance       => PrivTypes.ClassT'First,
         MaxFAR          => IandATypes.FarT'First);

   type ScreenConfigT is
      record
         IsDisplayed : Boolean;
         Data : DisplayedConfigT;
      end record;

   subtype SecondsStringI is Positive range 1..7;
   subtype SecondsStringT is String(SecondsStringI);

   subtype HrsMinsStringI is Positive range 1..5;
   subtype HrsMinsStringT is String(HrsMinsStringI);

   subtype ClassStringI is Positive range 1..12;
   subtype ClassStringT is String(ClassStringI);

   subtype FileSizeStringI is Positive range 1..15;
   subtype FileSizeStringT is String(FileSizeStringI);

   subtype FARStringI is Positive range 1..12;
   subtype FARStringT is String(ClassStringI);

   subtype AccessPolicyStringI is Positive range 1..12;
   subtype AccessPolicyStringT is String(AccessPolicyStringI);

   subtype StatsCountStringI is Positive range 1..10;
   subtype StatsCountStringT is String(StatsCountStringI);

   MsgString : constant MsgStringLookupT := MsgStringLookupT'
     ("                                           ",
      "WELCOME TO TIS                             ",
      "SYSTEM BUSY PLEASE WAIT                    ",
      "REMOVE TOKEN                               ",
      "CLOSE ENCLAVE DOOR                         ",
      "ENTER REQUIRED OPERATION                   ",
      "PERFORMING OPERATION PLEASE WAIT           ",
      "INVALID REQUEST: PLEASE ENTER NEW OPERATION",
      "INVALID DATA: PLEASE ENTER NEW OPERATION   ",
      "ARCHIVE FAILED: PLEASE ENTER NEW OPERATION ",
      "PLEASE INSERT ENROLMENT DATA FLOPPY        ",
      "VALIDATING ENROLMENT DATA PLEASE WAIT      ",
      "INVALID ENROLMENT DATA                     ",
      "INSERT BLANK FLOPPY                        ",
      "INSERT CONFIGURATION DATA FLOPPY           ");

   ------------------------------------------------------------------
   -- State
   --
   ------------------------------------------------------------------

   TheMsg              : MsgTextT;
   CurrentMsg          : MsgTextT;
   CurrentStats        : ScreenStatsT;
   CurrentConfig       : ScreenConfigT;
   CurrentDoorAlarm    : AlarmTypes.StatusT;
   CurrentLogAlarm     : AlarmTypes.StatusT;


   ------------------------------------------------------------------
   -- Local Operations
   ------------------------------------------------------------------

   ------------------------------------------------------------------
   -- WriteMessage
   --
   -- Description:
   --    Writes the message string to console.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure WriteMessage (OK :  out Boolean)
   --# global in     TheMsg;
   --#        in out CurrentMsg;
   --#           out Interfac.Output;
   --# derives CurrentMsg,
   --#         OK,
   --#         Interfac.Output from CurrentMsg,
   --#                               TheMsg;
   is
   begin

      if CurrentMsg /= TheMsg then
         Interfac.Write(Buffer => MsgString(TheMsg),
                         Colour => Interfac.BrightWhite,
                         Coord  => Interfac.XYCoordT'(0, 3),
                         OK     => OK);

         CurrentMsg := TheMsg;
      else
         OK := True;
      end if;

   end WriteMessage;


   ------------------------------------------------------------------
   -- WriteAlarms
   --
   -- Description:
   --    Writes the alarm states to console.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure WriteAlarms
     (NewDoorAlarm  : in     AlarmTypes.StatusT;
      NewAuditAlarm : in     AlarmTypes.StatusT;
      OK            :    out Boolean )
   --# global in out CurrentDoorAlarm;
   --#        in out CurrentLogAlarm;
   --#           out Interfac.Output;
   --# derives OK,
   --#         Interfac.Output  from CurrentDoorAlarm,
   --#                                NewDoorAlarm,
   --#                                CurrentLogAlarm,
   --#                                NewAuditAlarm &
   --#         CurrentDoorAlarm  from *,
   --#                                NewDoorAlarm &
   --#         CurrentLogAlarm   from *,
   --#                                NewAuditAlarm;
   is
      ConsoleOK : Boolean;
   begin
      OK := True;

      if NewDoorAlarm /= CurrentDoorAlarm then
         if NewDoorAlarm = AlarmTypes.Alarming then
            Interfac.Write(Buffer => "FAIL",
                            Colour => Interfac.Red,
                            Coord  => Interfac.XYCoordT'(15, 24),
                            OK     => ConsoleOK);
         else
            Interfac.Write(Buffer => "OK  ",
                            Colour => Interfac.Green,
                            Coord  => Interfac.XYCoordT'(15, 24),
                            OK     => ConsoleOK);
         end if;
         OK := ConsoleOK;
         CurrentDoorAlarm := NewDoorAlarm;
      end if;


      if NewAuditAlarm /= CurrentLogAlarm then
         if NewAuditAlarm = AlarmTypes.Alarming then
            Interfac.Write(Buffer => "FAIL",
                            Colour => Interfac.Red,
                            Coord  => Interfac.XYCoordT'(15, 26),
                            OK     => ConsoleOK);
         else
            Interfac.Write(Buffer => "OK  ",
                            Colour => Interfac.Green,
                            Coord  => Interfac.XYCoordT'(15, 26),
                            OK     => ConsoleOK);
         end if;
         CurrentLogAlarm := NewAuditAlarm;
         OK := OK or ConsoleOK;
      end if;

   end WriteAlarms;

   ------------------------------------------------------------------
   -- ClearConfigData
   --
   -- Description:
   --    Clears the Config Data display.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure ClearConfigData(OK : out Boolean)
   --# global out Interfac.Output;
   --# derives OK,
   --#         Interfac.Output from ;
   is
   begin

      Interfac.ClearRegion(Left   => 2,
                            Top    => 9,
                            Right  => 79,
                            Bottom => 18,
                            OK     => OK);

   end ClearConfigData;


   ------------------------------------------------------------------
   -- WriteConfigLabels
   --
   -- Description:
   --    Writes the labels for the Config data display to console.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure WriteConfigLabels(OK : out Boolean)
   --# global out Interfac.Output;
   --# derives OK,
   --#         Interfac.Output from ;
   is
      ConsoleOK : Boolean;
      Column1 : constant Interfac.ScreenXCoordT := 2;
      Column2 : constant Interfac.ScreenXCoordT := 39;

      Row1 : constant Interfac.ScreenYCoordT := 9;
      Row2 : constant Interfac.ScreenYCoordT := 10;
      Row3 : constant Interfac.ScreenYCoordT := 12;
      Row4 : constant Interfac.ScreenYCoordT := 13;
      Row5 : constant Interfac.ScreenYCoordT := 15;
      Row6 : constant Interfac.ScreenYCoordT := 16;
      Row7 : constant Interfac.ScreenYCoordT := 18;

   begin

      Interfac.Write(Buffer => "Latch Unlock Duration:",
                      Colour => Interfac.White,
                      Coord  => Interfac.XYCoordT'(Column1, Row1),
                      OK     => OK);

      Interfac.Write(Buffer => "Alarm Silent Duration:",
                      Colour => Interfac.White,
                      Coord  => Interfac.XYCoordT'(Column1, Row2),
                      OK     => ConsoleOK);
      OK := OK and ConsoleOK;

      Interfac.Write(Buffer => "Finger Wait Duration:",
                      Colour => Interfac.White,
                      Coord  => Interfac.XYCoordT'(Column2, Row1),
                      OK     => ConsoleOK);
      OK := OK and ConsoleOK;

      Interfac.Write(Buffer => "Token Removal Duration:",
                      Colour => Interfac.White,
                      Coord  => Interfac.XYCoordT'(Column2, Row2),
                      OK     => ConsoleOK);
      OK := OK and ConsoleOK;

      Interfac.Write(Buffer => "Access Policy:",
                      Colour => Interfac.White,
                      Coord  => Interfac.XYCoordT'(Column1, Row3),
                      OK     => ConsoleOK);
      OK := OK and ConsoleOK;

      Interfac.Write(Buffer => "Working Hours Start:",
                      Colour => Interfac.White,
                      Coord  => Interfac.XYCoordT'(Column2, Row3),
                      OK     => ConsoleOK);
      OK := OK and ConsoleOK;

      Interfac.Write(Buffer => "Working Hours End:",
                      Colour => Interfac.White,
                      Coord  => Interfac.XYCoordT'(Column2, Row4),
                      OK     => ConsoleOK);
      OK := OK and ConsoleOK;

      Interfac.Write(Buffer => "Authorisation Period:",
                      Colour => Interfac.White,
                      Coord  => Interfac.XYCoordT'(Column1, Row4),
                      OK     => ConsoleOK);
      OK := OK and ConsoleOK;

      Interfac.Write(Buffer => "Enclave Clearance:",
                      Colour => Interfac.White,
                      Coord  => Interfac.XYCoordT'(Column1, Row5),
                      OK     => ConsoleOK);
      OK := OK and ConsoleOK;

      Interfac.Write(Buffer => "Minimum Entry Class:",
                      Colour => Interfac.White,
                      Coord  => Interfac.XYCoordT'(Column1, Row6),
                      OK     => ConsoleOK);
      OK := OK and ConsoleOK;

      Interfac.Write(Buffer => "Min Preserved Log Size:",
                      Colour => Interfac.White,
                      Coord  => Interfac.XYCoordT'(Column2, Row5),
                      OK     => ConsoleOK);
      OK := OK and ConsoleOK;

      Interfac.Write(Buffer => "Alarm Threshold Size:",
                      Colour => Interfac.White,
                      Coord  => Interfac.XYCoordT'(Column2, Row6),
                      OK     => ConsoleOK);
      OK := OK and ConsoleOK;

      Interfac.Write(Buffer => "System Maximum FAR:",
                      Colour => Interfac.White,
                      Coord  => Interfac.XYCoordT'(Column1, Row7),
                      OK     => ConsoleOK);
      OK := OK and ConsoleOK;

   end WriteConfigLabels;

   ------------------------------------------------------------------
   -- WriteConfigData
   --
   -- Description:
   --    Writes the configuration data for the display to console.
   --    Only updates if there have been changed values.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure WriteConfigData( OK       :    out Boolean);
   procedure WriteConfigData( OK       :    out Boolean)
   --# global in     ConfigData.State;
   --#        in out CurrentConfig;
   --#           out Interfac.Output;
   --# derives OK,
   --#         Interfac.Output,
   --#         CurrentConfig    from CurrentConfig,
   --#                               ConfigData.State;
   is
      pragma SPARK_Mode (Off);  --  concatenation
      ConsoleOK : Boolean;

      LatchUnlock,
        AlarmSilent,
        FingerWait,
        TokenRemove,
        WorkStart,
        WorkEnd,
        AuthDuration : Clock.DurationT;

      Policy : ConfigData.AccessPolicyT;
      MinPreservedLog, AlarmThreshold : AuditTypes.FileSizeT;
      MinEntry, Clearance : PrivTypes.ClassT;
      MaxFAR : IandATypes.FarT;

      NewConfig : DisplayedConfigT;

      Column1 : constant Interfac.ScreenXCoordT := 25;
      Column2 : constant Interfac.ScreenXCoordT := 63;

      Row1 : constant Interfac.ScreenYCoordT := 9;
      Row2 : constant Interfac.ScreenYCoordT := 10;
      Row3 : constant Interfac.ScreenYCoordT := 12;
      Row4 : constant Interfac.ScreenYCoordT := 13;
      Row5 : constant Interfac.ScreenYCoordT := 15;
      Row6 : constant Interfac.ScreenYCoordT := 16;
      Row7 : constant Interfac.ScreenYCoordT := 18;


      ------------------------------------------------------------------
      -- SecondsString
      --
      -- Description:
      --    Converts a Duration to String in seconds,
      --    only applicable to ConfigData.DurationT which is <= 200 s.
      --
      -- Implementation Notes:
      --    Hidden due to use of Slicing.
      --
      ------------------------------------------------------------------
      function SecondsString (Value : ConfigData.DurationT)
                              return SecondsStringT
      is
         --# hide SecondsString;
         Str : SecondsStringT := "  0.0 s";
         ValueStr : String := ConfigData.DurationT'Image(Value);
      begin
         Str(5) := ValueStr(ValueStr'Last);
         if Value >= 10 then
            -- Know ValueStr is at least 3 characters.
            Str(6 - ValueStr'Last .. 3)
              := ValueStr(2 .. ValueStr'Last - 1);
         end if;
         return Str;
      end SecondsString;

      ------------------------------------------------------------------
      -- HrsMinsString
      --
      -- Description:
      --    Converts a Duration to String containing the hours and
      --    minutes component.
      --
      -- Implementation Notes:
      --    Hidden due to use of Slicing.
      --
      ------------------------------------------------------------------
      function HrsMinsString (Value : Clock.DurationT) return HrsMinsStringT
      is
      --# hide HrsMinsString;
      begin
         return Clock.PrintDuration(Value)(1..5);
      end HrsMinsString;

      ------------------------------------------------------------------
      -- FileSizeString
      --
      -- Description:
      --    Converts a File Size in kBytes to String.
      --
      -- Implementation Notes:
      --    Hidden due to use of 'Image.
      --
      ------------------------------------------------------------------
      function FileSizeString (Value : AuditTypes.FileSizeT)
                               return FileSizeStringT
      is
      --# hide FileSizeString;
         Data : String := AuditTypes.FileSizeT'Image(Value/2**10) & " kBytes";
         Result : FileSizeStringT := (others => ' ');
      begin
         Result(1 .. Data'Last - 1) := Data(2 .. Data'Last);
         return Result;
      end FileSizeString;

      ------------------------------------------------------------------
      -- AccessPolicyString
      --
      -- Description:
      --    Converts an access policy to String.
      --
      -- Implementation Notes:
      --    Hidden due to use of 'Image.
      --
      ------------------------------------------------------------------
      function AccessPolicyString (Value : ConfigData.AccessPolicyT)
                                   return AccessPolicyStringT
      is
      --# hide AccessPolicyString;
         Data : String := ConfigData.AccessPolicyT'Image(Value);
         Result : AccessPolicyStringT := (others => ' ');
      begin
         Result(1 .. Data'Last) := Data;
         return Result;
      end AccessPolicyString;

      ------------------------------------------------------------------
      -- ClassString
      --
      -- Description:
      --    Converts a class to String.
      --
      -- Implementation Notes:
      --    Hidden due to use of 'Image.
      --
      ------------------------------------------------------------------
      function ClassString (Value : PrivTypes.ClassT)
                            return ClassStringT
      is
      --# hide ClassString;
         Data : String := PrivTypes.ClassT'Image(Value);
         Result : ClassStringT := (others => ' ');
      begin
         Result(1 .. Data'Last) := Data;
         return Result;
      end ClassString;

      ------------------------------------------------------------------
      -- FARString
      --
      -- Description:
      --    Converts a FAR to String.
      --
      -- Implementation Notes:
      --    Hidden due to use of 'Image.
      --
      ------------------------------------------------------------------
      function FARString (Value : IandATypes.FarT)
                          return FARStringT
      is
      --# hide FARString;
         Data : String := IandATypes.FarT'Image(Value);
         Result : FARStringT := (others => ' ');
      begin
         Result(1 .. Data'Last - 1) := Data(2 .. Data'Last);
         return Result;
      end FARString;

      -------------------------------------------------------------------
      -- begin WriteConfigData
      -------------------------------------------------------------------
   begin

      ConfigData.TheDisplayFields
        (TheLatchUnlockDuration  => LatchUnlock,
         TheAlarmSilentDuration  => AlarmSilent,
         TheFingerWaitDuration   => FingerWait,
         TheTokenRemovalDuration => TokenRemove,
         TheEnclaveClearance     => Clearance,
         TheWorkingHoursStart    => WorkStart,
         TheWorkingHoursEnd      => WorkEnd,
         TheMaxAuthDuration      => AuthDuration,
         TheAccessPolicy         => Policy,
         TheMinEntryClass        => MinEntry,
         TheMinPreservedLogSize  => MinPreservedLog,
         TheAlarmThresholdSize   => AlarmThreshold,
         TheSystemMaxFar         => MaxFAR);

      NewConfig := DisplayedConfigT'
        (LatchUnlock     => LatchUnlock,
         AlarmSilent     => AlarmSilent,
         FingerWait      => FingerWait,
         TokenRemove     => TokenRemove,
         WorkStart       => WorkStart,
         WorkEnd         => WorkEnd,
         AuthDuration    => AuthDuration,
         Policy          => Policy,
         MinPreservedLog => MinPreservedLog,
         AlarmThreshold  => AlarmThreshold,
         MinEntry        => MinEntry,
         Clearance       => Clearance,
         MaxFAR          => MaxFAR);

      if not CurrentConfig.IsDisplayed or CurrentConfig.Data /= NewConfig then

         Interfac.ClearRegion(Left   => Column1,
                               Top    => Row1,
                               Right  => 38,
                               Bottom => Row7,
                               OK     => OK);

         Interfac.ClearRegion(Left   => Column2,
                               Top    => Row1,
                               Right  => 79,
                               Bottom => Row7,
                               OK     => ConsoleOK);
         OK := OK and ConsoleOK;

         Interfac.Write(Buffer => SecondsString(LatchUnlock),
                         Colour => Interfac.White,
                         Coord  => Interfac.XYCoordT'(Column1, Row1),
                         OK     => ConsoleOK);
         OK := OK and ConsoleOK;

         Interfac.Write(Buffer => SecondsString(AlarmSilent),
                         Colour => Interfac.White,
                         Coord  => Interfac.XYCoordT'(Column1, Row2),
                         OK     => ConsoleOK);
         OK := OK and ConsoleOK;

         Interfac.Write(Buffer => SecondsString(FingerWait),
                         Colour => Interfac.White,
                         Coord  => Interfac.XYCoordT'(Column2, Row1),
                         OK     => ConsoleOK);
         OK := OK and ConsoleOK;

         Interfac.Write(Buffer => SecondsString(TokenRemove),
                         Colour => Interfac.White,
                         Coord  => Interfac.XYCoordT'(Column2, Row2),
                         OK     => ConsoleOK);
         OK := OK and ConsoleOK;

         Interfac.Write(Buffer => AccessPolicyString(Policy),
                         Colour => Interfac.White,
                         Coord  => Interfac.XYCoordT'(Column1, Row3),
                         OK     => ConsoleOK);
         OK := OK and ConsoleOK;

         Interfac.Write(Buffer => HrsMinsString(WorkStart),
                         Colour => Interfac.White,
                         Coord  => Interfac.XYCoordT'(Column2, Row3),
                         OK     => ConsoleOK);
         OK := OK and ConsoleOK;

         Interfac.Write(Buffer => HrsMinsString(WorkEnd),
                         Colour => Interfac.White,
                         Coord  => Interfac.XYCoordT'(Column2, Row4),
                         OK     => ConsoleOK);
         OK := OK and ConsoleOK;

         Interfac.Write(Buffer => HrsMinsString(AuthDuration),
                         Colour => Interfac.White,
                         Coord  => Interfac.XYCoordT'(Column1, Row4),
                         OK     => ConsoleOK);
         OK := OK and ConsoleOK;

         Interfac.Write(Buffer => ClassString(Clearance),
                         Colour => Interfac.White,
                         Coord  => Interfac.XYCoordT'(Column1, Row5),
                         OK     => ConsoleOK);
         OK := OK and ConsoleOK;

         Interfac.Write(Buffer => ClassString(MinEntry),
                         Colour => Interfac.White,
                         Coord  => Interfac.XYCoordT'(Column1, Row6),
                         OK     => ConsoleOK);
         OK := OK and ConsoleOK;

         Interfac.Write(Buffer => FileSizeString(MinPreservedLog),
                         Colour => Interfac.White,
                         Coord  => Interfac.XYCoordT'(Column2, Row5),
                         OK     => ConsoleOK);
         OK := OK and ConsoleOK;

         Interfac.Write(Buffer => FileSizeString(AlarmThreshold),
                         Colour => Interfac.White,
                         Coord  => Interfac.XYCoordT'(Column2, Row6),
                         OK     => ConsoleOK);
         OK := OK and ConsoleOK;

         Interfac.Write(Buffer => FARString(MaxFAR),
                         Colour => Interfac.White,
                         Coord  => Interfac.XYCoordT'(Column1, Row7),
                         OK     => ConsoleOK);
         OK := OK and ConsoleOK;

         CurrentConfig.Data := NewConfig;

      else

         OK := True;

      end if;

   end WriteConfigData;

   ------------------------------------------------------------------
   -- ClearStats
   --
   -- Description:
   --    Clears the Stats display.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure ClearStats(OK : out Boolean)
   --# global out Interfac.Output;
   --# derives OK,
   --#         Interfac.Output from ;
   is
   begin

      Interfac.ClearRegion(Left   => 35,
                            Top    => 23,
                            Right  => 79,
                            Bottom => 26,
                            OK     => OK);

   end ClearStats;

   ------------------------------------------------------------------
   -- WriteStatsLabels
   --
   -- Description:
   --    Writes the labels for the Stats display to console.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure WriteStatsLabels(OK : out Boolean)
   --# global out Interfac.Output;
   --# derives OK,
   --#         Interfac.Output from ;
   is
      ConsoleOK : Boolean;
   begin

      Interfac.Write(Buffer => "BioChecks:",
                      Colour => Interfac.White,
                      Coord  => Interfac.XYCoordT'(35, 25),
                      OK     => OK);

      Interfac.Write(Buffer => "Entries:",
                      Colour => Interfac.White,
                      Coord  => Interfac.XYCoordT'(35, 26),
                      OK     => ConsoleOK);
      OK := OK and ConsoleOK;

      Interfac.Write(Buffer => "OK",
                      Colour => Interfac.White,
                      Coord  => Interfac.XYCoordT'(50, 23),
                      OK     => ConsoleOK);
      OK := OK and ConsoleOK;

      Interfac.Write(Buffer => "Fail",
                      Colour => Interfac.White,
                      Coord  => Interfac.XYCoordT'(65, 23),
                      OK     => ConsoleOK);
      OK := OK and ConsoleOK;

   end WriteStatsLabels;

   ------------------------------------------------------------------
   -- WriteStatsData
   --
   -- Description:
   --    Writes the data for the Stats display to console.
   --    Only updates changed values.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure WriteStatsData(TheStats : in     Stats.T;
                            OK       :    out Boolean)
   --# global in     CurrentStats;
   --#           out Interfac.Output;
   --# derives OK,
   --#         Interfac.Output from TheStats,
   --#                               CurrentStats;
   is
      ConsoleOK : Boolean;
      SuccessEntry,
        FailEntry,
        SuccessBio,
        FailBio    : Stats.StatsCount;

      ------------------------------------------------------------------
      -- StatsCountString
      --
      -- Description:
      --    Converts a Stats Count to String.
      --
      -- Implementation Notes:
      --    Hidden due to use of 'Image.
      --
      ------------------------------------------------------------------
      function StatsCountString (Value : Stats.StatsCount)
                                 return StatsCountStringT
      is
      --# hide StatsCountString;
         Data : String := Stats.StatsCount'Image(Value);
         Result : StatsCountStringT := (others => ' ');
      begin
         Result(1 .. Data'Last - 1) := Data(2 .. Data'Last);
         return Result;
      end StatsCountString;

   -----------------------------------------------------------
   -- begin WriteStatsData
   -----------------------------------------------------------
   begin

      if not CurrentStats.IsDisplayed or CurrentStats.Data /= TheStats then

         Stats.DisplayStats(TheStats     => TheStats,
                            SuccessEntry => SuccessEntry,
                            FailEntry    => FailEntry,
                            SuccessBio   => SuccessBio,
                            FailBio      => FailBio);

         Interfac.ClearRegion(Left   => 50,
                               Top    => 25,
                               Right  => 79,
                               Bottom => 26,
                               OK     => OK);

         Interfac.Write(Buffer => StatsCountString(SuccessEntry),
                         Colour => Interfac.White,
                         Coord  => Interfac.XYCoordT'(50, 26),
                         OK     => ConsoleOK);
         OK := OK and ConsoleOK;

         Interfac.Write(Buffer => StatsCountString(FailEntry),
                         Colour => Interfac.White,
                         Coord  => Interfac.XYCoordT'(65, 26),
                         OK     => ConsoleOK);
         OK := OK and ConsoleOK;

         Interfac.Write(Buffer => StatsCountString(SuccessBio),
                         Colour => Interfac.White,
                         Coord  => Interfac.XYCoordT'(50, 25),
                         OK     => ConsoleOK);
         OK := OK and ConsoleOK;

         Interfac.Write(Buffer => StatsCountString(FailBio),
                         Colour => Interfac.White,
                         Coord  => Interfac.XYCoordT'(65, 25),
                         OK     => ConsoleOK);
         OK := OK and ConsoleOK;

      else
         OK := True;
      end if;

   end WriteStatsData;

   ------------------------------------------------------------------
   -- WriteCurrentTime
   --
   -- Description:
   --    Writes the current time to the top right corner of the screen.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure WriteCurrentTime(OK : out Boolean)
   --# global in     Clock.Now;
   --#           out Interfac.Output;
   --# derives OK,
   --#         Interfac.Output from Clock.Now;
   is

      TheTime : Clock.TimeT;
   begin

      TheTime := Clock.GetNow;
      Interfac.Write(Buffer => Clock.PrintTime(TheTime),
                      Colour => Interfac.White,
                      Coord  => Interfac.XYCoordT'(58, 0),
                      OK     => OK);

   end WriteCurrentTime;

   ------------------------------------------------------------------
   -- Public Operations
   ------------------------------------------------------------------

   ------------------------------------------------------------------
   -- SetMessage
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------

   procedure SetMessage (Msg : in     MsgTextT)
   --# global in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in out TheMsg;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from TheMsg,
   --#                                 ConfigData.State,
   --#                                 Clock.Now,
   --#                                 Msg,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState &
   --#         TheMsg             from Msg;
   is
   begin
      if Msg /= TheMsg then
         AuditLog.AddElementToLog(
                ElementID   => AuditTypes.ScreenChanged,
                Severity    => AuditTypes.Information,
                User        => AuditTypes.NoUser,
                Description => MsgString(Msg)
                );
      end if;
      TheMsg := Msg;

   end SetMessage;

   ------------------------------------------------------------------
   -- UpdateScreen
   --
   -- Implementation Notes:
   --    The update is lazy to avoid adverse screen flicker.
   --
   ------------------------------------------------------------------

   procedure UpdateScreen
     (TheStats : in    Stats.T;
      TheAdmin : in    Admin.T)
   --# global in     TheMsg;
   --#        in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in     Door.State;
   --#        in out CurrentMsg;
   --#        in out CurrentDoorAlarm;
   --#        in out CurrentLogAlarm;
   --#        in out CurrentConfig;
   --#        in out CurrentStats;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#           out Interfac.Output;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from CurrentMsg,
   --#                                 TheMsg,
   --#                                 CurrentDoorAlarm,
   --#                                 CurrentLogAlarm,
   --#                                 CurrentConfig,
   --#                                 ConfigData.State,
   --#                                 TheStats,
   --#                                 CurrentStats,
   --#                                 Clock.Now,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Door.State,
   --#                                 TheAdmin &
   --#         CurrentMsg         from *,
   --#                                 TheMsg &
   --#         Interfac.Output   from CurrentMsg,
   --#                                 TheMsg,
   --#                                 CurrentDoorAlarm,
   --#                                 CurrentLogAlarm,
   --#                                 CurrentConfig,
   --#                                 ConfigData.State,
   --#                                 TheStats,
   --#                                 CurrentStats,
   --#                                 Clock.Now,
   --#                                 AuditLog.State,
   --#                                 Door.State,
   --#                                 TheAdmin &
   --#         CurrentDoorAlarm   from *,
   --#                                 Door.State &
   --#         CurrentLogAlarm  from *,
   --#                                 AuditLog.State &
   --#         CurrentConfig      from *,
   --#                                 TheAdmin,
   --#                                 ConfigData.State &
   --#         CurrentStats       from TheStats,
   --#                                 TheAdmin;
   is
      Unused   : Boolean;
      ScreenOK : Boolean;
      WriteOK  : Boolean;

      ShouldDisplayStats : Boolean;
      ShouldDisplayConfig : Boolean;

   begin
      WriteCurrentTime(OK => ScreenOK);

      WriteMessage(OK => WriteOK);
      ScreenOK := WriteOK and ScreenOK;

      WriteAlarms(NewDoorAlarm  => Door.TheDoorAlarm,
                  NewAuditAlarm => AuditLog.TheAuditAlarm,
                  OK            => WriteOK);

      ScreenOK := WriteOK and ScreenOK;

      -- Stats are only displayed if an administrator is present

      ShouldDisplayStats := Admin.IsPresent(TheAdmin => TheAdmin);

      if ShouldDisplayStats then
         if not CurrentStats.IsDisplayed then
            WriteStatsLabels(OK => WriteOK);
            ScreenOK := WriteOK and ScreenOK;

         end if;
         WriteStatsData(TheStats => TheStats,
                        OK       => WriteOK);
         ScreenOK := WriteOK and ScreenOK;

      else
         if CurrentStats.IsDisplayed then
            ClearStats(OK => WriteOK);
            ScreenOK := WriteOK and ScreenOK;

         end if;
      end if;

      CurrentStats := ScreenStatsT'(IsDisplayed => ShouldDisplayStats,
                                    Data        => TheStats);

      -- Config Data is only displayed if a security officer is present
      ShouldDisplayConfig := Admin.SecurityOfficerIsPresent(TheAdmin);

      if ShouldDisplayConfig then
         if not CurrentConfig.IsDisplayed then
            WriteConfigLabels(OK => WriteOK);
            ScreenOK := WriteOK and ScreenOK;

         end if;
         WriteConfigData(OK       => WriteOK);
         ScreenOK := WriteOK and ScreenOK;

      else
         if CurrentConfig.IsDisplayed then
            ClearConfigData(OK => WriteOK);
            ScreenOK := WriteOK and ScreenOK;

         end if;
      end if;
      CurrentConfig.IsDisplayed := ShouldDisplayConfig;

      if not ScreenOK then

         AuditLog.AddElementToLog
           ( ElementID   => AuditTypes.SystemFault,
             Severity    => AuditTypes.Warning,
             User        => AuditTypes.NoUser,
             Description => "Screen Update Failure"
             );

         --# accept F, 10, Unused, "Ineffective assignment expected here" &
         --#        F, 33, Unused, "Ineffective assignment expected here";
         ClearConfigData(OK => Unused);
         ClearStats(OK => Unused);

      end if;

   end UpdateScreen; -- flow error from Unused variable

   ------------------------------------------------------------------
   -- Init
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------

   procedure Init
     (IsEnrolled : in    Boolean)
   --# global in     ConfigData.State;
   --#        in     Clock.Now;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#           out CurrentMsg;
   --#           out TheMsg;
   --#           out Interfac.Output;
   --#           out CurrentDoorAlarm;
   --#           out CurrentLogAlarm;
   --#           out CurrentConfig;
   --#           out CurrentStats;
   --# derives CurrentMsg,
   --#         TheMsg,
   --#         Interfac.Output   from IsEnrolled &
   --#         CurrentDoorAlarm,
   --#         CurrentLogAlarm,
   --#         CurrentConfig,
   --#         CurrentStats       from  &
   --#         AuditLog.State,
   --#         AuditLog.FileState from ConfigData.State,
   --#                                 Clock.Now,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 IsEnrolled;
   is

      ScreenOK,
      WriteOK : Boolean;
      LocalStats : Stats.T;

   begin
      Interfac.Init(ScreenOK);

      Stats.Init(LocalStats);

      CurrentStats := ScreenStatsT'(IsDisplayed => False,
                                    Data        => LocalStats);

      CurrentConfig := ScreenConfigT'(IsDisplayed => False,
                                      Data        => NullConfigData);
      -- No need to display the Stats;

      -- This is a fiddle to ensure that the alarms are printed.
      CurrentDoorAlarm  := AlarmTypes.Alarming;
      CurrentLogAlarm := AlarmTypes.Alarming;

      WriteAlarms(NewDoorAlarm  => AlarmTypes.Silent,
                  NewAuditAlarm => AlarmTypes.Silent,
                  OK            => WriteOK);
      ScreenOK := ScreenOK and WriteOK;


      CurrentMsg := Clear;

      if IsEnrolled then
         TheMsg := WelcomeAdmin;
      else
         TheMsg := Clear;
      end if;
      WriteMessage(OK => WriteOK);
      ScreenOK := ScreenOK and WriteOK;

      if not ScreenOK then

         AuditLog.AddElementToLog
           ( ElementID   => AuditTypes.SystemFault,
             Severity    => AuditTypes.Warning,
             User        => AuditTypes.NoUser,
             Description => "Screen Initialisation Failure"
             );

      end if;

   end Init;

end Screen;
