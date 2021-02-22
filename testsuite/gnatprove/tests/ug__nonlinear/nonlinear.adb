procedure Nonlinear (X, Y, Z : Positive; R1, R2 : out Natural) with
  SPARK_Mode,
  Pre  => Y > Z,
  Post => R1 <= R2
is
begin
   R1 := X / Y;
   R2 := X / Z;
end Nonlinear;
