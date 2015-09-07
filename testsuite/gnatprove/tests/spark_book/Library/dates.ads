pragma SPARK_Mode;

package Dates is
   type Year_Type   is range 2000 .. 2099;
   type Month_Type  is range 1 .. 12;
   type Day_Type    is range 1 .. 31;  -- Days can be in this range and yet still be illegal.

   type Hour_Type   is range 0 .. 23;
   type Minute_Type is range 0 .. 59;
   type Second_Type is range 0 .. 59;

   -- Represents the number of date values in the range between 2000-01-01 and 2099-12-31.
   subtype Day_Count_Type is Natural range 0 .. 36525;

   -- Represents the number of steps between two dates.
   subtype Day_Advance_Type is Integer range -(Day_Count_Type'Last - 1) .. (Day_Count_Type'Last - 1);

   type Date is private;
   type Time is private;
   type Datetime is private;

   -- Used to initialize a objects with a default (well defined) values.
   function Default_Date return Date;
   function Default_Time return Time;
   function Default_Datetime return Datetime;

   -- Used to initialize Date objects with user specified values.
   procedure Create_Date
     (Year     : in  Year_Type;
      Month    : in  Month_Type;
      Day      : in  Day_Type;
      New_Date : out Date;
      Valid    : out Boolean)
   with
     Depends => ( (New_Date, Valid) => (Year, Month, Day) );

   -- This subprogram can't fail so it doesn't need to return a Valid indicator. Thus it can be a function.
   function Create_Time
     (Hour   : in Hour_Type;
      Minute : in Minute_Type;
      Second : in Second_Type) return Time;

   -- This subprogram can't fail so it doesn't need to return a Valid indicator. Thus it can be a function.
   function Create_Datetime(Date_Part : in Date; Time_Part : in Time) return Datetime;

   -- Accessor methods.
   function Get_Year  (Current_Date : Date) return Year_Type;
   function Get_Month (Current_Date : Date) return Month_Type;
   function Get_Day   (Current_Date : Date) return Day_Type;

   function Get_Hour  (Current_Time : Time) return Hour_Type;
   function Get_Minute(Current_Time : Time) return Minute_Type;
   function Get_Second(Current_Time : Time) return Second_Type;

   function Get_Date(Current_Moment : Datetime) return Date;
   function Get_Time(Current_Moment : Datetime) return Time;

   -- Advances a date by the specified amount. It is permitted to advance by a negative amount.
   -- If an attempt is made to advance off the end of the valid range of dates, Valid is set to False and Current_Date
   -- is set to the last allowed date in the direction of advancement.
   --
   procedure Advance(Current_Date : in out Date; By : in Day_Advance_Type; Valid : out Boolean)
   with
     Depends => ( (Current_Date, Valid) => (Current_Date, By) );

   -- Needed for the Post condition of Is_Before could be useful for other things.
   function Maximum_Datetime return Datetime
   with
     Inline;

   function Minimum_Datetime return Datetime
   with
     Inline;

   -- Returns True if Past comes before Future.
   function Is_Before(Past : Datetime; Future : Datetime) return Boolean
   with
     Post => (if Is_Before'Result then ((Past /= Maximum_Datetime) and (Future /= Minimum_Datetime)));

private

   type Date is
      record
         Day   : Day_Type;
         Month : Month_Type;
         Year  : Year_Type;
      end record;

   type Time is
      record
         Hour   : Hour_Type;
         Minute : Minute_Type;
         Second : Second_Type;
      end record;

   type Datetime is
      record
         Date_Part : Date;
         Time_Part : Time;
      end record;

   function Maximum_Datetime return Datetime is
     (Datetime'(Date_Part => (Day => 31, Month => Month_Type'Last, Year => Year_Type'Last),
                Time_Part => (Hour => Hour_Type'Last, Minute => Minute_Type'Last, Second => Second_Type'Last)));

   function Minimum_Datetime return Datetime is
     (Datetime'(Date_Part => (Day =>  1, Month => Month_Type'First, Year => Year_Type'First),
                Time_Part => (Hour => Hour_Type'First, Minute => Minute_Type'First, Second => Second_Type'First)));

end Dates;
