package Time with SPARK_Mode is

   -- Units of time
   days_in_year              : constant := 366;
   hours_in_day              : constant := 24;
   minutes_in_hour           : constant := 60;
   seconds_in_day            : constant := 86400;
   seconds_in_hour           : constant := 3600;
   seconds_in_minute         : constant := 60;

   -- Other useful conversions
   -- Days information.
   days_in_days100           : constant := 100;
   days_in_days10            : constant := 10;

   -- Seconds information.
   secs_in_hours10           : constant := 36000;
   secs_in_hours1            : constant := 3600;
   secs_in_mins10            : constant := 600;
   secs_in_mins1             : constant := 60;
   secs_in_secs10            : constant := 10;

   nanosecs_in_sec           : constant := 1_000_000_000;
   nanosecs_in_tenth_sec     : constant :=   100_000_000;
   nanosecs_in_hundredth_sec : constant :=    10_000_000;

   nanosecs_in_millisec      : constant :=     1_000_000;
   nanosecs_in_microsec      : constant :=         1_000;

   millisecs_in_sec          : constant :=         1_000;

   YEAR_DAYS                 : constant := 365;
   LEAP_DAYS                 : constant := 366;

   subtype milliseconds_t is Integer
      range 0 .. 1000 * seconds_in_day - 1;

   subtype year_t is Natural range 0 .. 9999;
   subtype month_t is Natural range 1 .. 12;
   subtype day_t is Natural range 1 .. 31;

   subtype day_of_year_t is Natural
                                 range 0 .. LEAP_DAYS;
   subtype hour_of_day_t is Natural
                                 range 0 .. hours_in_day - 1;
   subtype minute_of_hour_t is Natural
                                 range 0 .. minutes_in_hour - 1;
   subtype second_of_minute_t is Natural
                                 range 0 .. seconds_in_minute - 1;
   subtype second_of_day_t is Natural
                                 range 0 .. seconds_in_day - 1;
   subtype nanopart_of_whole_t is Natural
                                 range 0 .. nanosecs_in_sec - 1;
   subtype days_in_year_t is day_of_year_t
                                 range YEAR_DAYS .. LEAP_DAYS;

   type timestamp_t is record
      day_of_year : day_of_year_t;
      seconds     : second_of_day_t;
      nanoseconds : nanopart_of_whole_t;
   end record;

   type t is record
      valid    : Boolean;
      year     : year_t;
      day      : day_of_year_t;
      second   : second_of_day_t;
      fraction : nanopart_of_whole_t;
   end record;

   procedure add_DDS_duration_seconds (time_in  : in     t;
                                       seconds  : in     Integer;
                                       time_out :    out t);

end Time;
