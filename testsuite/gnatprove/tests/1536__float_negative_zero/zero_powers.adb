package body Zero_Powers with SPARK_Mode is

   procedure Minus_One (Y : out Real) is
      X : Real := Real'Copy_Sign (0.0, Sign);
   begin
      Y := X ** (-1); --@DIVISION_CHECK:FAIL
   end Minus_One;

   procedure Minus_Two (Y : out Real) is
      X : Real := Real'Copy_Sign (0.0, Sign);
   begin
      Y := X ** (-2); --@DIVISION_CHECK:FAIL
   end Minus_Two;

   procedure Minus_Three (Y : out Real) is
      X : Real := Real'Copy_Sign (0.0, Sign);
   begin
      Y := X ** (-3); --@DIVISION_CHECK:FAIL
   end Minus_Three;
end Zero_Powers;
