package Dates with SPARK_Mode is

   pragma Elaborate_Body;

   subtype Year_Number is Integer range 1 .. 2399;

   function Is_Leap_Year (Year : Year_Number) return Boolean is
     (Year mod 4 = 0 and (Year mod 400 not in 100 | 200 | 300));

   subtype Date_Range is Integer range 1 .. 876216;

   type Date_Type is record
      Day_Of_Common_Era : Date_Range;
   end record;

end Dates;
