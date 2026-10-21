--  Keep N dynamic so exponentiation uses Floating_power instead of being
--  expanded into multiplications and division by the translator.

procedure Power_Neg3 (X : Float; N : Integer) with
  SPARK_Mode,
  Pre => X = 2.0 and then N = -3
is
   Y : constant Float := X ** N; --@DIVISION_CHECK:PASS @FLOAT_OVERFLOW_CHECK:PASS
begin
   pragma Assert (Y = 0.125); --@ASSERT:PASS
   pragma Assert (Y = 0.25); --@ASSERT:FAIL
end Power_Neg3;
