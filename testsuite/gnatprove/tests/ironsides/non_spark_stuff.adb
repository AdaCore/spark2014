with Ada.Unchecked_Conversion;

with Interfaces.C;

package body Non_Spark_Stuff is

   --  Local constants

   type Time_Rep is new Long_Long_Integer;
   type Time is new Time_Rep;

   subtype Year_Number  is Integer range 1901 .. 2399;
   subtype Month_Number is Integer range 1 .. 12;
   subtype Day_Number   is Integer range 1 .. 31;

   subtype Day_Duration is Duration range 0.0 .. 86_400.0;

   Days_In_Month : constant array (Month_Number) of Day_Number :=
                     (31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31);
   --  Days in month for non-leap year, leap year case is adjusted in code

   Invalid_Time_Zone_Offset : Long_Integer;
   pragma Import (C, Invalid_Time_Zone_Offset, "__gnat_invalid_tzoff");

   Nano         : constant := 1_000_000_000;
   Nano_F       : constant := 1_000_000_000.0;
   Nanos_In_Day : constant := 86_400_000_000_000;
   Secs_In_Day  : constant := 86_400;

   Ada_Min_Year          : constant Year_Number := Year_Number'First;
   Secs_In_Four_Years    : constant := (3 * 365 + 366) * Secs_In_Day;
   Secs_In_Non_Leap_Year : constant := 365 * Secs_In_Day;
   Nanos_In_Four_Years   : constant := Secs_In_Four_Years * Nano;

   --------------------------
   -- Leap seconds control --
   --------------------------

   Flag : Integer;
   pragma Import (C, Flag, "__gl_leap_seconds_support");
   --  This imported value is used to determine whether the compilation had
   --  binder flag "-y" present which enables leap seconds. A value of zero
   --  signifies no leap seconds support while a value of one enables support.

   Leap_Support : constant Boolean := (Flag = 1);
   --  Flag to controls the usage of leap seconds in all Ada.Calendar routines

   Leap_Seconds_Count : constant Natural := 25;

   --  Lower and upper bound of Ada time. The zero (0) value of type Time is
   --  positioned at year 2150. Note that the lower and upper bound account
   --  for the non-leap centennial years.

   Ada_Low  : constant Time_Rep := -(61 * 366 + 188 * 365) * Nanos_In_Day;
   Ada_High : constant Time_Rep :=  (60 * 366 + 190 * 365) * Nanos_In_Day;

   --  Even though the upper bound of time is 2399-12-31 23:59:59.999999999
   --  UTC, it must be increased to include all leap seconds.

   Ada_High_And_Leaps : constant Time_Rep :=
     Ada_High + Time_Rep (Leap_Seconds_Count) * Nano;

   --  Two constants used in the calculations of elapsed leap seconds.
   --  End_Of_Time is later than Ada_High in time zone -28. Start_Of_Time
   --  is earlier than Ada_Low in time zone +28.

   End_Of_Time   : constant Time_Rep :=
     Ada_High + Time_Rep (3) * Nanos_In_Day;
   Start_Of_Time : constant Time_Rep :=
     Ada_Low - Time_Rep (3) * Nanos_In_Day;

   --  The Unix lower time bound expressed as nanoseconds since the start of
   --  Ada time in UTC.

   Unix_Min : constant Time_Rep :=
     Ada_Low + Time_Rep (17 * 366 + 52 * 365) * Nanos_In_Day;

   --  The Unix upper time bound expressed as nanoseconds since the start of
   --  Ada time in UTC.

   Unix_Max : constant Time_Rep :=
     Ada_Low + Time_Rep (34 * 366 + 102 * 365) * Nanos_In_Day +
     Time_Rep (Leap_Seconds_Count) * Nano;

   Epoch_Offset : constant Time_Rep := (136 * 365 + 44 * 366) * Nanos_In_Day;
   --  The difference between 2150-1-1 UTC and 1970-1-1 UTC expressed in
   --  nanoseconds. Note that year 2100 is non-leap.

   Cumulative_Days_Before_Month :
     constant array (Month_Number) of Natural :=
       (0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334);

   --  The following table contains the hard time values of all existing leap
   --  seconds. The values are produced by the utility program xleaps.adb. This
   --  must be updated when additional leap second times are defined.

   Leap_Second_Times : constant array (1 .. Leap_Seconds_Count) of Time_Rep :=
     (-5601484800000000000,
      -5585587199000000000,
      -5554051198000000000,
      -5522515197000000000,
      -5490979196000000000,
      -5459356795000000000,
      -5427820794000000000,
      -5396284793000000000,
      -5364748792000000000,
      -5317487991000000000,
      -5285951990000000000,
      -5254415989000000000,
      -5191257588000000000,
      -5112287987000000000,
      -5049129586000000000,
      -5017593585000000000,
      -4970332784000000000,
      -4938796783000000000,
      -4907260782000000000,
      -4859827181000000000,
      -4812566380000000000,
      -4765132779000000000,
      -4544207978000000000,
      -4449513577000000000,
      -4339180776000000000);

   -----------------------------
   -- Cumulative_Leap_Seconds --
   -----------------------------

   procedure Cumulative_Leap_Seconds
     (Start_Date    : Time_Rep;
      End_Date      : Time_Rep;
      Elapsed_Leaps : out Natural;
      Next_Leap     : out Time_Rep)
   is
      End_Index   : Positive;
      End_T       : Time_Rep := End_Date;
      Start_Index : Positive;
      Start_T     : Time_Rep := Start_Date;

   begin
      --  Both input dates must be normalized to UTC

      pragma Assert (Leap_Support and then End_Date >= Start_Date);

      Next_Leap := End_Of_Time;

      --  Make sure that the end date does not exceed the upper bound
      --  of Ada time.

      if End_Date > Ada_High then
         End_T := Ada_High;
      end if;

      --  Remove the sub seconds from both dates

      Start_T := Start_T - (Start_T mod Nano);
      End_T   := End_T   - (End_T   mod Nano);

      --  Some trivial cases:
      --                     Leap 1 . . . Leap N
      --  ---+========+------+############+-------+========+-----
      --     Start_T  End_T                       Start_T  End_T

      if End_T < Leap_Second_Times (1) then
         Elapsed_Leaps := 0;
         Next_Leap     := Leap_Second_Times (1);
         return;

      elsif Start_T > Leap_Second_Times (Leap_Seconds_Count) then
         Elapsed_Leaps := 0;
         Next_Leap     := End_Of_Time;
         return;
      end if;

      --  Perform the calculations only if the start date is within the leap
      --  second occurrences table.

      if Start_T <= Leap_Second_Times (Leap_Seconds_Count) then

         --    1    2                  N - 1   N
         --  +----+----+--  . . .  --+-------+---+
         --  | T1 | T2 |             | N - 1 | N |
         --  +----+----+--  . . .  --+-------+---+
         --         ^                   ^
         --         | Start_Index       | End_Index
         --         +-------------------+
         --             Leaps_Between

         --  The idea behind the algorithm is to iterate and find two
         --  closest dates which are after Start_T and End_T. Their
         --  corresponding index difference denotes the number of leap
         --  seconds elapsed.

         Start_Index := 1;
         loop
            exit when Leap_Second_Times (Start_Index) >= Start_T;
            Start_Index := Start_Index + 1;
         end loop;

         End_Index := Start_Index;
         loop
            exit when End_Index > Leap_Seconds_Count
              or else Leap_Second_Times (End_Index) >= End_T;
            End_Index := End_Index + 1;
         end loop;

         if End_Index <= Leap_Seconds_Count then
            Next_Leap := Leap_Second_Times (End_Index);
         end if;

         Elapsed_Leaps := End_Index - Start_Index;

      else
         Elapsed_Leaps := 0;
      end if;
   end Cumulative_Leap_Seconds;

   ---------------------
   -- UTC_Time_Offset --
   ---------------------

   function UTC_Time_Offset
     (Date        : Time;
      Is_Historic : Boolean) return Long_Integer
   is
      --  The following constants denote February 28 during non-leap centennial
      --  years, the units are nanoseconds.

      T_2100_2_28 : constant Time_Rep := Ada_Low +
                      (Time_Rep (49 * 366 + 150 * 365 + 59) * Secs_In_Day +
                       Time_Rep (Leap_Seconds_Count)) * Nano;

      T_2200_2_28 : constant Time_Rep := Ada_Low +
                      (Time_Rep (73 * 366 + 226 * 365 + 59) * Secs_In_Day +
                       Time_Rep (Leap_Seconds_Count)) * Nano;

      T_2300_2_28 : constant Time_Rep := Ada_Low +
                      (Time_Rep (97 * 366 + 302 * 365 + 59) * Secs_In_Day +
                       Time_Rep (Leap_Seconds_Count)) * Nano;

      --  56 years (14 leap years + 42 non-leap years) in nanoseconds:

      Nanos_In_56_Years : constant := (14 * 366 + 42 * 365) * Nanos_In_Day;

      type int_Pointer  is access all Interfaces.C.int;
      type long_Pointer is access all Interfaces.C.long;

      type time_t is
        range -(2 ** (Standard'Address_Size - Integer'(1))) ..
              +(2 ** (Standard'Address_Size - Integer'(1)) - 1);
      type time_t_Pointer is access all time_t;

      procedure localtime_tzoff
        (timer       : time_t_Pointer;
         is_historic : int_Pointer;
         off         : long_Pointer);
      pragma Import (C, localtime_tzoff, "__gnat_localtime_tzoff");
      --  This routine is a interfacing wrapper around the library function
      --  __gnat_localtime_tzoff. Parameter 'timer' represents a Unix-based
      --  time equivalent of the input date. If flag 'is_historic' is set, this
      --  routine would try to calculate to the best of the OS's abilities the
      --  time zone offset that was or will be in effect on 'timer'. If the
      --  flag is set to False, the routine returns the current time zone
      --  regardless of what 'timer' designates. Parameter 'off' captures the
      --  UTC offset of 'timer'.

      Adj_Cent : Integer;
      Date_N   : Time_Rep;
      Flag     : aliased Interfaces.C.int;
      Offset   : aliased Interfaces.C.long;
      Secs_T   : aliased time_t;

   --  Start of processing for UTC_Time_Offset

   begin
      Date_N := Time_Rep (Date);

      --  Dates which are 56 years apart fall on the same day, day light saving
      --  and so on. Non-leap centennial years violate this rule by one day and
      --  as a consequence, special adjustment is needed.

      Adj_Cent :=
        (if    Date_N <= T_2100_2_28 then 0
         elsif Date_N <= T_2200_2_28 then 1
         elsif Date_N <= T_2300_2_28 then 2
         else                             3);

      if Adj_Cent > 0 then
         Date_N := Date_N - Time_Rep (Adj_Cent) * Nanos_In_Day;
      end if;

      --  Shift the date within bounds of Unix time

      while Date_N < Unix_Min loop
         Date_N := Date_N + Nanos_In_56_Years;
      end loop;

      while Date_N >= Unix_Max loop
         Date_N := Date_N - Nanos_In_56_Years;
      end loop;

      --  Perform a shift in origins from Ada to Unix

      Date_N := Date_N - Unix_Min;

      --  Convert the date into seconds

      Secs_T := time_t (Date_N / Nano);

      --  Determine whether to treat the input date as historical or not. A
      --  value of "0" signifies that the date is NOT historic.

      Flag := (if Is_Historic then 1 else 0);

      localtime_tzoff
        (Secs_T'Unchecked_Access,
         Flag'Unchecked_Access,
         Offset'Unchecked_Access);

      return Long_Integer (Offset);
   end UTC_Time_Offset;

   ------------------------------
   -- Check_Within_Time_Bounds --
   ------------------------------

   procedure Check_Within_Time_Bounds (T : Time_Rep) is
   begin
      if Leap_Support then
         if T < Ada_Low or else T > Ada_High_And_Leaps then
            raise Program_Error;
         end if;
      else
         if T < Ada_Low or else T > Ada_High then
            raise Program_Error;
         end if;
      end if;
   end Check_Within_Time_Bounds;

   -------------
   -- Is_Leap --
   -------------

   function Is_Leap (Year : Year_Number) return Boolean is
   begin
      --  Leap centennial years

      if Year mod 400 = 0 then
         return True;

      --  Non-leap centennial years

      elsif Year mod 100 = 0 then
         return False;

      --  Regular years

      else
         return Year mod 4 = 0;
      end if;
   end Is_Leap;

   --------------------------
   -- Duration_To_Time_Rep --
   --------------------------

   function Duration_To_Time_Rep is
     new Ada.Unchecked_Conversion (Duration, Time_Rep);
   --  Convert a duration value into a time representation value

   --------------------
   -- Format_Time_Of --
   --------------------

   function Format_Time_Of
     (Year         : Year_Number;
      Month        : Month_Number;
      Day          : Day_Number;
      Day_Secs     : Day_Duration;
      Hour         : Integer;
      Minute       : Integer;
      Second       : Integer;
      Sub_Sec      : Duration;
      Leap_Sec     : Boolean;
      Use_Day_Secs : Boolean;
      Is_Historic  : Boolean;
      Time_Zone    : Long_Integer) return Time
   is
      Count         : Integer;
      Elapsed_Leaps : Natural;
      Next_Leap_N   : Time_Rep;
      Res_N         : Time_Rep;
      Rounded_Res_N : Time_Rep;

   begin
      --  Step 1: Check whether the day, month and year form a valid date

      if Day > Days_In_Month (Month)
        and then (Day /= 29 or else Month /= 2 or else not Is_Leap (Year))
      then
         raise Program_Error;
      end if;

      --  Start accumulating nanoseconds from the low bound of Ada time

      Res_N := Ada_Low;

      --  Step 2: Year processing and centennial year adjustment. Determine
      --  the number of four year segments since the start of Ada time and
      --  the input date.

      Count := (Year - Year_Number'First) / 4;

      for Four_Year_Segments in 1 .. Count loop
         Res_N := Res_N + Nanos_In_Four_Years;
      end loop;

      --  Note that non-leap centennial years are automatically considered
      --  leap in the operation above. An adjustment of several days is
      --  required to compensate for this.

      if Year > 2300 then
         Res_N := Res_N - Time_Rep (3) * Nanos_In_Day;

      elsif Year > 2200 then
         Res_N := Res_N - Time_Rep (2) * Nanos_In_Day;

      elsif Year > 2100 then
         Res_N := Res_N - Time_Rep (1) * Nanos_In_Day;
      end if;

      --  Add the remaining non-leap years

      Count := (Year - Year_Number'First) mod 4;
      Res_N := Res_N + Time_Rep (Count) * Secs_In_Non_Leap_Year * Nano;

      --  Step 3: Day of month processing. Determine the number of days
      --  since the start of the current year. Do not add the current
      --  day since it has not elapsed yet.

      Count := Cumulative_Days_Before_Month (Month) + Day - 1;

      --  The input year is leap and we have passed February

      if Is_Leap (Year)
        and then Month > 2
      then
         Count := Count + 1;
      end if;

      Res_N := Res_N + Time_Rep (Count) * Nanos_In_Day;

      --  Step 4: Hour, minute, second and sub second processing

      if Use_Day_Secs then
         Res_N := Res_N + Duration_To_Time_Rep (Day_Secs);

      else
         Res_N :=
           Res_N + Time_Rep (Hour * 3_600 + Minute * 60 + Second) * Nano;

         if Sub_Sec = 1.0 then
            Res_N := Res_N + Time_Rep (1) * Nano;
         else
            Res_N := Res_N + Duration_To_Time_Rep (Sub_Sec);
         end if;
      end if;

      --  At this point, the generated time value should be withing the
      --  bounds of Ada time.

      Check_Within_Time_Bounds (Res_N);

      --  Step 4: Time zone processing. At this point we have built an
      --  arbitrary time value which is not related to any time zone.
      --  For simplicity, the time value is normalized to GMT, producing
      --  a uniform representation which can be treated by arithmetic
      --  operations for instance without any additional corrections.

      declare
         Cur_Off   : constant Long_Integer :=
           UTC_Time_Offset (Time (Res_N), Is_Historic);
         Cur_Res_N : constant Time_Rep :=
           Res_N - Time_Rep (Cur_Off) * Nano;
         Off       : constant Long_Integer :=
           UTC_Time_Offset (Time (Cur_Res_N), Is_Historic);

      begin
         Res_N := Res_N - Time_Rep (Off) * Nano;
      end;

      --  Step 5: Leap seconds processing in GMT

      if Leap_Support then
         Cumulative_Leap_Seconds
           (Start_Of_Time, Res_N, Elapsed_Leaps, Next_Leap_N);

         Res_N := Res_N + Time_Rep (Elapsed_Leaps) * Nano;

         --  An Ada 2005 caller requesting an explicit leap second or an
         --  Ada 95 caller accounting for an invisible leap second.

         if Leap_Sec or else Res_N >= Next_Leap_N then
            Res_N := Res_N + Time_Rep (1) * Nano;
         end if;
      end if;

      return Time (Res_N);
   end Format_Time_Of;

   -------------
   -- Time_Of --
   -------------

   function Time_Of
     (Year    : Year_Number;
      Month   : Month_Number;
      Day     : Day_Number;
      Seconds : Day_Duration := 0.0) return Time
   is
      --  The values in the following constants are irrelevant, they are just
      --  placeholders; the choice of constructing a Day_Duration value is
      --  controlled by the Use_Day_Secs flag.

      H  : constant Integer := 1;
      M  : constant Integer := 1;
      Se : constant Integer := 1;
      Ss : constant Duration := 0.1;

   begin

      --  Even though the input time zone is UTC (0), the flag Use_TZ will
      --  ensure that Split picks up the local time zone.

      return
        Format_Time_Of
          (Year         => Year,
           Month        => Month,
           Day          => Day,
           Day_Secs     => Seconds,
           Hour         => H,
           Minute       => M,
           Second       => Se,
           Sub_Sec      => Ss,
           Leap_Sec     => False,
           Use_Day_Secs => True,
           Is_Historic  => True,
           Time_Zone    => 0);
   end Time_Of;

   EPOCH_START : constant Time :=  Time_Of (1970, 1, 1, 0.0);
   --THIS MUST BE CALLED WITH ALL PARAMETERS HAVING VALID VALUES OR IT WILL THROW
   --AN EXCEPTION

   function Get_Time_Of
     (Year,
      Month,
      Day,
      Hour,
      Minute,
      Second : Natural)
      return Unsigned_Types.Unsigned32
   is
   begin
      return Unsigned_Types.Unsigned32
        (Time_Of
           (Year,
            Month,
            Day,
            Duration(3600 * Hour + 60 * Minute + Second)) - EPOCH_START);
   end Get_Time_Of;
end Non_Spark_Stuff;
