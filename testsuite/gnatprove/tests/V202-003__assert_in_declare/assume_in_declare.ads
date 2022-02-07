package Assume_In_Declare with SPARK_Mode is

   function Rand (X : Integer) return Integer with Import;

   function F return Integer is
      ((declare
         Result : constant Integer := Rand (0);
         pragma Assume (Result > 10);
       begin Result));

end Assume_In_Declare;
