package body Time with SPARK_Mode is

   function ddays_in_year (year : year_t) return Days_In_Year_T
   is
      result : days_in_year_t;
   begin

      if Year = 340 then
         result := days_in_year_t'Last;
      else
         result := days_in_year_t'First;
      end if;
      return result;

   end ddays_in_year;

   procedure add_DDS_duration_seconds (time_in  : in     t;
                                       seconds  : in     Integer;
                                       time_out :    out t)
   is
      -- Temporary Time storage.
      temp_time         : t;
      -- Temporary time variables for 't' generation.
      temp_seconds      : Integer;
      temp_days         : Integer;
      temp_years        : Integer;
      temp_days_in_year : Integer;
   begin
      -- Get a local copy of the reference time to help SPARK SIMPLIFICATION.
      temp_time := time_in;
      -- Get a local copy of the supplied time.
      temp_years := Integer (temp_time.year);
      -- Get a local copy of the supplied DDS Duration seconds.
      while seconds >= (Integer (ddays_in_year (year_t (temp_years)) * seconds_in_day))
      loop
         null;
      end loop;
   end Add_DDS_Duration_Seconds;

end Time;
