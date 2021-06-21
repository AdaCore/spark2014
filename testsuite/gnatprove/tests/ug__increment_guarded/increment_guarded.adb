procedure Increment_Guarded (X : in out Integer) with
  SPARK_Mode,
  Pre => X < Integer'Last
is
begin
   X := X + 1;
end Increment_Guarded;
