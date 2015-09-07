pragma SPARK_Mode;

package body Dates is

   function Maximum_Date return Date is
     (Date'(Day => 31, Month => Month_Type'Last, Year => Year_Type'Last));

   function Minimum_Date return Date is
     (Date'(Day =>  1, Month => Month_Type'First, Year => Year_Type'First));

   -- Return True if the given year is a leap year.
   -- The method used here is correct for all years in the range of Year_Type.
   --
   function Is_Leap_Year(Year : Year_Type) return Boolean is
      Result : Boolean := False;
   begin
      if Year mod 4 = 0 then
         Result := True;
      end if;
      return Result;
   end Is_Leap_Year;


   -- Return the length in days of the given month. The effect of leap years is considered.
   function Get_Month_Length(Year : Year_Type; Month : Month_Type) return Day_Type
   with
     Post =>
       (if Month =  1 then  Get_Month_Length'Result = 31) and
       (if Month =  2 then (Get_Month_Length'Result = 28 or Get_Month_Length'Result = 29)) and
       (if Month =  3 then  Get_Month_Length'Result = 31) and
       (if Month =  4 then  Get_Month_Length'Result = 30) and
       (if Month =  5 then  Get_Month_Length'Result = 31) and
       (if Month =  6 then  Get_Month_Length'Result = 30) and
       (if Month =  7 then  Get_Month_Length'Result = 31) and
       (if Month =  8 then  Get_Month_Length'Result = 31) and
       (if Month =  9 then  Get_Month_Length'Result = 30) and
       (if Month = 10 then  Get_Month_Length'Result = 31) and
       (if Month = 11 then  Get_Month_Length'Result = 30) and
       (if Month = 12 then  Get_Month_Length'Result = 31);

   function Get_Month_Length(Year : Year_Type; Month : Month_Type) return Day_Type is

      type Month_Length_Lookup_Table is array(Month_Type) of Day_Type;
      Month_Length : constant Month_Length_Lookup_Table :=
        (31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31);

      Length : Day_Type;
   begin
      if Is_Leap_Year(Year) and Month = 2 then
         Length := 29;
      else
         Length := Month_Length(Month);
      end if;
      return Length;
   end Get_Month_Length;


   -- Return True if the given date is a valid date.
   function Is_Valid_Date(Year : Year_Type; Month : Month_Type; Day : Day_Type) return Boolean is
      Result : Boolean := True;
   begin
      if Day > Get_Month_Length(Year, Month) then
         Result := False;
      end if;
      return Result;
   end Is_Valid_Date;


   -- Advance the given date ahead by one day.
   procedure One_Day_Forward(Current_Date : in out Date)
   with
     Depends => (Current_Date =>+ null),
     Pre => Current_Date /= Maximum_Date
   is
   begin
      if Current_Date.Day < Get_Month_Length(Current_Date.Year, Current_Date.Month) then
         Current_Date.Day := Current_Date.Day + 1;
      else
         if Current_Date.Month /= Month_Type'Last then
            Current_Date.Day   := 1;
            Current_Date.Month := Current_Date.Month + 1;
         else
            Current_Date.Day   := 1;
            Current_Date.Month := 1;
            Current_Date.Year  := Current_Date.Year + 1;
         end if;
      end if;
   end One_Day_Forward;


   -- Backs up the given date by one day.
   procedure One_Day_Backward(Current_Date : in out Date)
   with
     Depends => (Current_Date =>+ null),
     Pre => Current_Date /= Minimum_Date
   is
   begin
      if Current_Date.Day /= 1 then
         Current_Date.Day := Current_Date.Day - 1;
      else
         if Current_Date.Month /= Month_Type'First then
            Current_Date.Month := Current_Date.Month - 1;
            Current_Date.Day   := Get_Month_Length(Current_Date.Year, Current_Date.Month);
         else
            Current_Date.Year  := Current_Date.Year - 1;
            Current_Date.Month := Month_Type'Last;
            Current_Date.Day   := 31;
         end if;
      end if;
   end One_Day_Backward;


   ----------------------
   -- Visible subprograms
   ----------------------

   function Default_Date return Date is
   begin
      return Date'(Year => Year_Type'First, Month => Month_Type'First, Day => 1);
   end Default_Date;


   function Default_Time return Time is
   begin
      return Time'(Hour => 0, Minute => 0, Second => 0);
   end Default_Time;


   function Default_Datetime return Datetime is
   begin
      return Datetime'(Date_Part => Default_Date, Time_Part => Default_Time);
   end Default_Datetime;


   procedure Create_Date
     (Year     : in Year_Type;
      Month    : in Month_Type;
      Day      : in Day_Type;
      New_Date : out Date;
      Valid    : out Boolean) is
   begin
      if Is_Valid_Date(Year, Month, Day) then
         New_Date.Year  := Year;
         New_Date.Month := Month;
         New_Date.Day   := Day;
         Valid          := True;
      else
         -- Use the default date if the given date is invalid (SPARK requires some sort of initialization).
         New_Date       := Default_Date;
         Valid          := False;
      end if;
   end Create_Date;


   function Create_Time
     (Hour   : in Hour_Type;
      Minute : in Minute_Type;
      Second : in Second_Type) return Time is
   begin
      return Time'(Hour, Minute, Second);
   end Create_Time;


   function Create_Datetime(Date_Part : in Date; Time_Part : in Time) return Datetime is
   begin
      return Datetime'(Date_Part, Time_Part);
   end Create_Datetime;


   function Get_Year(Current_Date : Date) return Year_Type is
   begin
      return Current_Date.Year;
   end Get_Year;


   function Get_Month(Current_Date : Date) return Month_Type is
   begin
      return Current_Date.Month;
   end Get_Month;


   function Get_Day(Current_Date : Date) return Day_Type is
   begin
      return Current_Date.Day;
   end Get_Day;


   function Get_Hour(Current_Time : Time) return Hour_Type is
   begin
      return Current_Time.Hour;
   end Get_Hour;


   function Get_Minute(Current_Time : Time) return Minute_Type is
   begin
      return Current_Time.Minute;
   end Get_Minute;


   function Get_Second(Current_Time : Time) return Second_Type is
   begin
      return Current_Time.Second;
   end Get_Second;


   function Get_Date(Current_Moment : Datetime) return Date is
   begin
      return Current_Moment.Date_Part;
   end Get_Date;


   function Get_Time(Current_Moment : Datetime) return Time is
   begin
      return Current_Moment.Time_Part;
   end Get_Time;


   procedure Advance(Current_Date : in out Date; By : in Day_Advance_Type; Valid : out Boolean) is
      Steps : Day_Advance_Type;
   begin
      Valid := True;
      if By >= 0 then
         Steps := By;
         for I in Day_Advance_Type range 1 .. Steps loop
            if Current_Date = Maximum_Date then
               Valid := False;
               exit;
            end if;

            pragma Loop_Invariant(Current_Date /= Maximum_Date);

            One_Day_Forward(Current_Date);
         end loop;
      else
         Steps := -By;
         for I in Day_Advance_Type range 1 .. Steps loop
            if Current_Date = Minimum_Date then
               Valid := False;
               exit;
            end if;

            pragma Loop_Invariant(Current_Date /= Minimum_Date);

            One_Day_Backward(Current_Date);
         end loop;
      end if;
   end Advance;


   function Is_Before(Past : Datetime; Future : Datetime) return Boolean is
      Result : Boolean := False;
   begin
      if Past.Date_Part.Year < Future.Date_Part.Year then
         Result := True;
      elsif Past.Date_Part.Year = Future.Date_Part.Year then
         if Past.Date_Part.Month < Future.Date_Part.Month then
            Result := True;
         elsif Past.Date_Part.Month = Future.Date_Part.Month then
            if Past.Date_Part.Day < Future.Date_Part.Day then
               Result := True;
            elsif Past.Date_Part.Day = Future.Date_Part.Day then
               if Past.Time_Part.Hour < Future.Time_Part.Hour then
                  Result := True;
               elsif Past.Time_Part.Hour = Future.Time_Part.Hour then
                  if Past.Time_Part.Minute < Future.Time_Part.Minute then
                     Result := True;
                  elsif Past.Time_Part.Minute = Future.Time_Part.Minute then
                     if Past.Time_Part.Second < Future.Time_Part.Second then
                        Result := True;
                     end if;
                  end if;
               end if;
            end if;
         end if;
      end if;
      return Result;
   end Is_Before;

end Dates;
