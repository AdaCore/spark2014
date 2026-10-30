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

   procedure Minus_Four (Y : out Real) is
      X : Real := Real'Copy_Sign (0.0, Sign);
   begin
      Y := X ** (-4); --@DIVISION_CHECK:FAIL
   end Minus_Four;

   procedure Named_Exponent (Y : out Real) is
      X : Real := Real'Copy_Sign (0.0, Sign);
      N : constant Integer := -1;
   begin
      Y := X ** N; --@DIVISION_CHECK:FAIL
   end Named_Exponent;

   procedure Dynamic_Exponent (N : Integer; Y : out Real) is
      X : Real := Real'Copy_Sign (0.0, Sign);
   begin
      Y := X ** N; --@DIVISION_CHECK:FAIL
   end Dynamic_Exponent;

   procedure Zero_Exponent (Y : out Real) is
      X : Real := Real'Copy_Sign (0.0, Sign);
   begin
      Y := X ** 0; --@DIVISION_CHECK:NONE
   end Zero_Exponent;

   procedure Plus_One (Y : out Real) is
      X : Real := Real'Copy_Sign (0.0, Sign);
   begin
      Y := X ** 1; --@DIVISION_CHECK:NONE
   end Plus_One;

   procedure Plus_Two (Y : out Real) is
      X : Real := Real'Copy_Sign (0.0, Sign);
   begin
      Y := X ** 2; --@DIVISION_CHECK:NONE
   end Plus_Two;

   procedure Plus_Three (Y : out Real) is
      X : Real := Real'Copy_Sign (0.0, Sign);
   begin
      Y := X ** 3; --@DIVISION_CHECK:NONE
   end Plus_Three;

   procedure Divide (Y : out Real) is
      X : Real := Real'Copy_Sign (0.0, Sign);
   begin
      Y := 1.0 / X; --@DIVISION_CHECK:FAIL
   end Divide;

   procedure Remainder (Y : out Real) is
      X : Real := Real'Copy_Sign (0.0, Sign);
   begin
      Y := Real'Remainder (1.0, X); --@DIVISION_CHECK:FAIL
   end Remainder;

   procedure Nonzero (Y : out Real) is
      X : Real := Sign;
   begin
      Y := X ** (-1);
      pragma Assert (Y = X);
      Y := X ** (-2);
      pragma Assert (Y = 1.0);
      Y := X ** (-3);
      pragma Assert (Y = X);
      Y := 1.0 / X;
      pragma Assert (Y = X);
      Y := Real'Remainder (1.0, X);
      pragma Assert (Y = 0.0);
   end Nonzero;

   procedure Underflow (Y : out Real) is
      X : Real := Real'Copy_Sign (Real'Model_Small, Sign);
   begin
      --  Cubing a nonzero operand can also produce a signed zero
      Y := X ** (-3); --@DIVISION_CHECK:FAIL
   end Underflow;
end Zero_Powers;
