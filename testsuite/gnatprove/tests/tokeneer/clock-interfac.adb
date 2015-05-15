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
-- Clock.Interfac
--
-- Description:
--    Interfac to the system clock.
--
-- Implementation Notes:
--     This packge body is not presented to the SPARK Examiner.
------------------------------------------------------------------
with Ada.Calendar;
use Ada.Calendar;

package body Clock.Interfac
  with SPARK_Mode => Off
is

   ------------------------------------------------------------------
   -- Convert
   --
   -- Description:
   --    Converts Calendar.Time to Clock.TimeT
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   function Convert (T : Ada.Calendar.Time) return Clock.TimeT is
      Year  : Ada.Calendar.Year_Number;
      Month : Ada.Calendar.Month_Number;
      Day   : Ada.Calendar.Day_Number;
      Sec   : Duration;
   begin
      Ada.Calendar.Split
        (Date    => T,
         Year    => Year,
         Month   => Month,
         Day     => Day,
         Seconds => Sec);

      -- force truncating not rounding to ensure MilliSec doesn't overflow
      if Sec > 0.0005 then
         Sec := Sec - 0.0005;
      end if;

      return Clock.TimeT'
        (Year     => Clock.YearsT(Year),
         Month    => Clock.MonthsT(Month),
         Day      => Clock.DaysT(Day),
         MilliSec => Clock.MillisecsT(Sec * Clock.MilliSecsInSec));
   end Convert;

   ------------------------------------------------------------------
   -- TheTime
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   function TheTime return Clock.TimeT is (Convert (Ada.Calendar.Clock));

   ------------------------------------------------------------------
   -- AddDuration
   --
   -- Implementation Notes:
   --     If the time is not valid the duration is not added.
   --     If the addition causes an overflow then the duration is not added.
   --
   ------------------------------------------------------------------
   function AddDuration (T : Clock.TimeT ; D : Clock.DurationT)
                        return Clock.TimeT
   is
      LocalTime : Ada.Calendar.Time;
   begin
      LocalTime := (Duration(D) / 10) +
        Ada.Calendar.Time_Of
        (Year    => Ada.Calendar.Year_Number(T.Year),
         Month   => Ada.Calendar.Month_Number(T.Month),
         Day     => Ada.Calendar.Day_Number(T.Day),
         Seconds => Ada.Calendar.Day_Duration
         (Duration(T.MilliSec) / 1000));

      return Convert(LocalTime);

   exception
      when Ada.Calendar.Time_Error =>
         return T;
   end AddDuration;

   ------------------------------------------------------------------
   -- IsValidTime
   --
   -- Description:
   --    If the time can be converted to a system time then it is valid.
   --
   ------------------------------------------------------------------
   function IsValidTime (T : Clock.TimeT) return Boolean is
      LocalTime : Ada.Calendar.Time;
   begin
      LocalTime :=
        Ada.Calendar.Time_Of
        (Year    => Ada.Calendar.Year_Number(T.Year),
         Month   => Ada.Calendar.Month_Number(T.Month),
         Day     => Ada.Calendar.Day_Number(T.Day),
         Seconds => Ada.Calendar.Day_Duration( Duration(T.MilliSec) / 1000));

      return True;

   exception
      when Ada.Calendar.Time_Error =>
         return False;
   end IsValidTime;

end Clock.Interfac;
