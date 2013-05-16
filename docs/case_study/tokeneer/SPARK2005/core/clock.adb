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
-- Implementation Notes:
--    None.
--
------------------------------------------------------------------
with Clock.Interface,
     BasicTypes;

use type BasicTypes.Unsigned32T;

package body Clock
--# own Now is in Clock.Interface.Now;
is

   ------------------------------------------------------------------
   -- Types and constants
   --
   ------------------------------------------------------------------
      MilliSecsInMin : constant := 60 * MilliSecsInSec;
      MilliSecsInHr : constant := 60 * MilliSecsInMin;
   ------------------------------------------------------------------
   -- State
   --
   ------------------------------------------------------------------
   CurrentTime : TimeT;


   ------------------------------------------------------------------
   -- Private Operations
   ------------------------------------------------------------------

   ------------------------------------------------------------------
   -- SetStringSegment
   --
   -- Definition:
   --    Sets the section of the string S from SStart to SEnd with
   --    the String representation of the Value.
   --    Pads to the left with '0'.
   --    Truncates if Value is too big to fit.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure SetStringSegment
     ( S      : in out String;
       Value  : in     Natural;
       SStart : in     Positive;
       SEnd   : in     Positive)
   --# derives S from *,
   --#                Value,
   --#                SEnd,
   --#                SStart;
   --# pre S'Last >= SEnd and S'First <= SStart;
   is
      V : Natural;
   begin

      V := Value;

      for I in reverse Positive range SStart .. SEnd loop
         --# assert I <= SEnd and I >= SStart
         --#        and I <= S'Last and I >= S'First
         --#        and V in Natural ;
         S(I) := Character'Val(Character'Pos('0') + (V mod 10));
         V    := V / 10;
      end loop;

   end SetStringSegment;

   ------------------------------------------------------------------
   -- Public Operations
   ------------------------------------------------------------------

   ------------------------------------------------------------------
   -- Poll
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------

   procedure Poll
   --# global in     Interface.Now;
   --#           out CurrentTime;
   --# derives CurrentTime from Interface.Now;
   is
   begin
      CurrentTime := Interface.TheTime;
   end Poll;

   ------------------------------------------------------------------
   -- TheCurrentTime
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------

   function TheCurrentTime return TimeT
   is
   begin
      return CurrentTime;
   end TheCurrentTime;

   ------------------------------------------------------------------
   -- GetNow
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------

   function GetNow return TimeT
   --# global Interface.Now;
   is
   begin
      return Interface.TheTime;
   end GetNow;

   ------------------------------------------------------------------
   -- GreaterThan
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------

   function GreaterThan ( Left, Right : TimeT ) return Boolean
   is
   begin
      return Left.Year > Right.Year
        or (Left.Year = Right.Year
            and Left.Month > Right.Month )
        or (Left.Year = Right.Year
            and Left.Month = Right.Month
            and Left.Day > Right.Day)
        or (Left.Year = Right.Year
            and Left.Month = Right.Month
            and Left.Day = Right.Day
            and Left.MilliSec > Right.MilliSec);
   end GreaterThan;

   ------------------------------------------------------------------
   -- LessThan
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------

   function LessThan ( Left, Right : TimeT ) return Boolean
   is
   begin
      return Left.Year < Right.Year
        or (Left.Year = Right.Year
            and Left.Month < Right.Month )
        or (Left.Year = Right.Year
            and Left.Month = Right.Month
            and Left.Day < Right.Day)
        or (Left.Year= Right.Year
            and Left.Month = Right.Month
            and Left.Day = Right.Day
            and Left.MilliSec < Right.MilliSec);
   end LessThan;

   ------------------------------------------------------------------
   -- GreaterThanOrEqual
   --
   -- Implemention Notes:
   --    None.
   --
   ------------------------------------------------------------------

   function GreaterThanOrEqual ( Left, Right : TimeT ) return Boolean
   is
   begin
       return GreaterThan (Left, Right) or Left = Right;
   end GreaterThanOrEqual;

   ------------------------------------------------------------------
   -- LessThanOrEqual
   --
   -- Implemention Notes:
   --    None.
   --
   ------------------------------------------------------------------

   function LessThanOrEqual ( Left, Right : TimeT ) return Boolean
   is
   begin
       return LessThan (Left, Right) or Left = Right;
   end LessThanOrEqual;

   ------------------------------------------------------------------
   -- ConstructTime
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure ConstructTime
     (Year    : in     BasicTypes.Unsigned32T;
      Month   : in     BasicTypes.Unsigned32T;
      Day     : in     BasicTypes.Unsigned32T;
      Hour    : in     BasicTypes.Unsigned32T;
      Min     : in     BasicTypes.Unsigned32T;
      TheTime :    out TimeT;
      Success :    out Boolean)
   is
   begin
      if BasicTypes.Unsigned32T(YearsT'First) <= Year and
            Year <= BasicTypes.Unsigned32T(YearsT'Last) and
            BasicTypes.Unsigned32T(MonthsT'First) <= Month and
            Month <= BasicTypes.Unsigned32T(MonthsT'Last) and
            BasicTypes.Unsigned32T(DaysT'First) <= Day and
            Day <= BasicTypes.Unsigned32T(DaysT'Last) and
            BasicTypes.Unsigned32T(HoursT'First) <= Hour and
            Hour <= BasicTypes.Unsigned32T(HoursT'Last) and
            BasicTypes.Unsigned32T(MinutesT'First) <= Min and
            Min <= BasicTypes.Unsigned32T(MinutesT'Last) then


         TheTime := TimeT'
           (Year => YearsT(Year),
            Month => MonthsT(Month),
            Day => DaysT(Day),
            MilliSec => MilliSecsT(Hour) * MilliSecsInHr
                        + MilliSecsT(Min) * MilliSecsInMin);

         if Interface.IsValidTime(TheTime) then
            Success := True;
         else
            TheTime := ZeroTime;
            Success := False;
         end if;
      else
         TheTime := ZeroTime;
         Success := False;
      end if;
   end ConstructTime;

   ------------------------------------------------------------------
   -- SplitTime
   --
   -- Implementation Notes:
   --    This always rounds down.
   --
   ------------------------------------------------------------------
   procedure SplitTime
     (TheTime : in     TimeT;
      Year    :    out YearsT;
      Month   :    out MonthsT;
      Day     :    out DaysT;
      Hour    :    out HoursT;
      Min     :    out MinutesT)
   is

   begin
      Year  := TheTime.Year;
      Month := TheTime.Month;
      Day   := TheTime.Day;
      Hour  := HoursT (TheTime.MilliSec / MilliSecsInHr);
      Min   := MinutesT ((TheTime.MilliSec mod MilliSecsInHr )
                        / MilliSecsInMin);
   end SplitTime;

   ------------------------------------------------------------------
   -- StartOfDay
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   function StartOfDay (TheTime : TimeT) return TimeT
   is
   begin
      return TimeT'(Year => TheTime.Year,
                    Month => TheTime.Month,
                    Day => TheTime.Day,
                    MilliSec => MilliSecsT'First);
   end StartOfDay;


   ------------------------------------------------------------------
   -- PrintDuration
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   function PrintDuration (TheDuration : DurationT ) return DurationTextT
   is
      LocalText : DurationTextT := "hh:mm:ss.s";
      FirstHourIndex    : constant TimeTextI := 1;
      LastHourIndex     : constant TimeTextI := 2;

      FirstMinIndex     : constant TimeTextI := 4;
      LastMinIndex      : constant TimeTextI := 5;

      FirstSecIndex     : constant TimeTextI := 7;
      LastSecIndex      : constant TimeTextI := 8;

      TenthSecIndex     : constant TimeTextI := 10;

      TenthSecsInSec     : constant := 10;
      TenthSecsInMin     : constant := 60 * TenthSecsInSec;
      TenthSecsInHr      : constant := 60 * TenthSecsInMin;
   begin

      SetStringSegment(LocalText,
                       Natural(TheDuration / TenthSecsInHr),
                       FirstHourIndex,
                       LastHourIndex);

      SetStringSegment(LocalText,
                       Natural((TheDuration mod TenthSecsInHr)
                               / TenthSecsInMin),
                       FirstMinIndex,
                       LastMinIndex);

      SetStringSegment(LocalText,
                       Natural((TheDuration mod TenthSecsInMin)
                               / TenthSecsInSec),
                       FirstSecIndex,
                       LastSecIndex);

      SetStringSegment(LocalText,
                       Natural(TheDuration mod TenthSecsInSec),
                       TenthSecIndex,
                       TenthSecIndex);

      return LocalText;
   end PrintDuration;

   ------------------------------------------------------------------
   -- PrintTime
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   function PrintTime (TheTime : TimeT ) return TimeTextT
   is
      LocalText : TimeTextT := "yyyy-mm-dd hh:mm:ss.s";

      FirstYearIndex    : constant TimeTextI := 1;
      LastYearIndex     : constant TimeTextI := 4;

      FirstMonthIndex   : constant TimeTextI := 6;
      LastMonthIndex    : constant TimeTextI := 7;

      FirstDayIndex     : constant TimeTextI := 9;
      LastDayIndex      : constant TimeTextI := 10;

      FirstHourIndex    : constant TimeTextI := 12;
      LastHourIndex     : constant TimeTextI := 13;

      FirstMinIndex     : constant TimeTextI := 15;
      LastMinIndex      : constant TimeTextI := 16;

      FirstSecIndex     : constant TimeTextI := 18;
      LastSecIndex      : constant TimeTextI := 19;

      TenthSecIndex     : constant TimeTextI := 21;

   begin
      --# assert LocalText'First = TimeTextI'First and
      --#        LocalText'Last = TimeTextI'Last;

      SetStringSegment(LocalText,
                       Natural(TheTime.Year),
                       FirstYearIndex,
                       LastYearIndex);

      SetStringSegment(LocalText,
                       Natural(TheTime.Month),
                       FirstMonthIndex,
                       LastMonthIndex);

      SetStringSegment(LocalText,
                       Natural(TheTime.Day),
                       FirstDayIndex,
                       LastDayIndex);

      SetStringSegment(LocalText,
                       Natural(TheTime.MilliSec / MilliSecsInHr),
                       FirstHourIndex,
                       LastHourIndex);

      SetStringSegment(LocalText,
                       Natural((TheTime.MilliSec mod MilliSecsInHr)
                               / MilliSecsInMin),
                       FirstMinIndex,
                       LastMinIndex);

      SetStringSegment(LocalText,
                       Natural((TheTime.MilliSec mod MilliSecsInMin)
                               / MilliSecsInSec),
                       FirstSecIndex,
                       LastSecIndex);

      SetStringSegment(LocalText,
                       Natural((TheTime.MilliSec mod MilliSecsInSec)
                               / MilliSecsInTenthSec),
                       TenthSecIndex,
                       TenthSecIndex);

      return LocalText;
   end PrintTime;

   ------------------------------------------------------------------
   -- AddDuration
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   function AddDuration
     (TheTime : TimeT; TheDuration : DurationT ) return TimeT
   is
   begin
      return Interface.AddDuration(TheTime, TheDuration);

   end AddDuration;


end Clock;







