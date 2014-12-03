procedure Increment_Full (X : in out Integer) with
  SPARK_Mode,
  Global  => null,
  Depends => (X => X),
  Pre     => X < Integer'Last,
  Post    => X = X'Old + 1
is
begin
   X := X + 1;
end Increment_Full;
