pragma SPARK_Mode;
procedure Expo (X : in out Float)
  with Pre => X in -3.0 .. 3.0
is
begin
   X := X ** (-3); --@DIVISION_CHECK:FAIL
end Expo;
