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
-- Clock
--
-- Description:
--    Provides a "current time" for each system cycle.
--
------------------------------------------------------------------
with BasicTypes;

-- # inherit Clock.Interface;
--# inherit BasicTypes;

package Clock
--# own CurrentTime;
--#     in Now;
is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------

   ------------------------------------------------------------------
   -- Time
   --
   -- Description:
   --      Internal representation of time.
   --
   -- Traceunit : C.Clock.Time
   -- Traceto : FD.Types.Time
   ------------------------------------------------------------------
   type TimeT is private;

   ZeroTime : constant TimeT;

   type YearsT      is range 1901 .. 2099;
   type MonthsT     is range 1 .. 12;
   type DaysT       is range 1 .. 31;
   type HoursT      is range 0 .. 23;
   type MinutesT    is range 0 .. 59;
   ------------------------------------------------------------------
   -- Duration
   --
   -- Description:
   --    Duration in 1/10 seconds.
   --    The range allows 24 hours to be represented.
   ------------------------------------------------------------------
   type DurationT is range 0 .. 864000;

   ------------------------------------------------------------------
   -- TimeText
   -- DurationText
   --
   -- Description:
   --    Textual representation of time used in audit records.
   --    Times are displayed as "yyyy-mm-dd hh:mm:ss.s"
   --    Durations are displayed as "hh:mm:ss.s"
   ------------------------------------------------------------------
   subtype TimeTextI is Positive range 1 .. 21;
   subtype TimeTextT is String(TimeTextI);

   subtype DurationTextI is Positive range 1 .. 10;
   subtype DurationTextT is String(DurationTextI);

   ------------------------------------------------------------------
   -- Poll
   --
   -- Description:
   --    Reads the system clock, and updates the internal CurrentTime.
   --
   -- Traceunit: C.Clock.Poll
   -- Traceto: FD.Interface.PollTime
   ------------------------------------------------------------------

   procedure Poll;
   --# global in     Now;
   --#           out CurrentTime;
   --# derives CurrentTime from Now;

   ------------------------------------------------------------------
   -- TheCurrentTime
   --
   -- Description:
   --    Returns CurrentTime recorded at the last poll.
   --
   -- Traceunit: C.Clock.TheCurrentTime
   -- Traceto: FD.RealWorld.State
   ------------------------------------------------------------------

   function TheCurrentTime return TimeT;
   --# global CurrentTime;

   ------------------------------------------------------------------
   -- GetNow
   --
   -- Description:
   --    Returns the system time now.
   --
   -- Traceunit: C.Clock.GetNow
   -- Traceto: FD.MonitoredRealWorld.State
   ------------------------------------------------------------------

   function GetNow return TimeT;
   --# global Now;


   ------------------------------------------------------------------
   -- GreaterThan
   --
   -- Description:
   --    Boolean function implementing > on the private Type Time.
   --
   -- Traceunit: C.Clock.GreaterThan
   --
   ------------------------------------------------------------------

   function GreaterThan ( Left, Right : TimeT ) return Boolean;

   ------------------------------------------------------------------
   -- LessThan
   --
   -- Description:
   --    Boolean function implementing < on the private Type Time.
   --
   -- Traceunit: C.Clock.LessThan
   --
   ------------------------------------------------------------------

   function LessThan ( Left, Right : TimeT ) return Boolean;

   ------------------------------------------------------------------
   -- GreaterThanOrEqual
   --
   -- Description:
   --    Boolean function implementing >= on the private Type Time.
   --
   -- Traceunit: C.Clock.GreaterThanOrEqual
   --
   ------------------------------------------------------------------

   function GreaterThanOrEqual ( Left, Right : TimeT ) return Boolean;

   ------------------------------------------------------------------
   -- LessThanOrEqual
   --
   -- Description:
   --    Boolean function implementing <= on the private Type Time.
   --
   -- Traceunit: C.Clock.LessThanOrEqual
   --
   ------------------------------------------------------------------

   function LessThanOrEqual ( Left, Right : TimeT ) return Boolean;

   ------------------------------------------------------------------
   -- ConstructTime
   --
   -- Description:
   --    Constructs a time from raw constituent parts. If the time is not
   --    valid then the Success flag is set to false.
   --
   -- Traceunit: C.Clock.ConstructTime
   --
   ------------------------------------------------------------------
   procedure ConstructTime
     (Year    : in     BasicTypes.Unsigned32T;
      Month   : in     BasicTypes.Unsigned32T;
      Day     : in     BasicTypes.Unsigned32T;
      Hour    : in     BasicTypes.Unsigned32T;
      Min     : in     BasicTypes.Unsigned32T;
      TheTime :    out TimeT;
      Success :    out Boolean);
   --# derives TheTime,
   --#         Success from Year,
   --#                      Month,
   --#                      Day,
   --#                      Hour,
   --#                      Min;

   ------------------------------------------------------------------
   -- SplitTime
   --
   -- Description:
   --    Decomposes a time into its constituent parts.
   --
   -- Traceunit: C.Clock.SplitTime
   --
   ------------------------------------------------------------------
   procedure SplitTime
     (TheTime : in     TimeT;
      Year    :    out YearsT;
      Month   :    out MonthsT;
      Day     :    out DaysT;
      Hour    :    out HoursT;
      Min     :    out MinutesT);
   --# derives Year,
   --#         Month,
   --#         Day,
   --#         Hour,
   --#         Min   from TheTime;

   ------------------------------------------------------------------
   -- StartOfDay
   --
   -- Description:
   --    Converts the time to the start of the day.
   --
   -- Traceunit: C.Clock.StartOfDay
   --
   ------------------------------------------------------------------
   function StartOfDay (TheTime : TimeT) return TimeT;

   ------------------------------------------------------------------
   -- PrintDuration
   --
   -- Description:
   --    Converts a duration to Text for display.
   --
   -- Traceunit: C.Clock.PrintDuration
   --
   ------------------------------------------------------------------
   function PrintDuration (TheDuration : DurationT ) return DurationTextT;

   ------------------------------------------------------------------
   -- PrintTime
   --
   -- Description:
   --    Converts a time to Text for display.
   --
   -- Traceunit: C.Clock.PrintText
   --
   ------------------------------------------------------------------
   function PrintTime (TheTime : TimeT ) return TimeTextT;

   ------------------------------------------------------------------
   -- AddDuration
   --
   -- Description:
   --    Adds a duration to a time.
   --
   -- Traceunit: C.Clock.AddDuration
   --
   ------------------------------------------------------------------
   function AddDuration
     (TheTime : TimeT; TheDuration : DurationT ) return TimeT;

private

   MilliSecsInTenthSec : constant := 100;
   MilliSecsInSec      : constant := 1000;

   type MilliSecsT    is range 0 .. DurationT'Last * MilliSecsInTenthSec - 1 ;

   type TimeT is record
      Year      : YearsT;
      Month     : MonthsT;
      Day       : DaysT;
      MilliSec  : MilliSecsT;
   end record;

   ZeroTime : constant TimeT :=
     TimeT'(Year => YearsT'First,
            Month => MonthsT'First,
            Day => DaysT'First,
            MilliSec => MilliSecsT'First);


end Clock;







