procedure Incr (X : in out Integer) with
  SPARK_Mode,
  Post => X = X'Old + 1  --  @COUNTEREXAMPLE
is
begin
   X := X - 1;  --  @COUNTEREXAMPLE
end Incr;
