procedure Increment_Loop (X : in out Integer; N : Natural) with
  SPARK_Mode,
  Pre  => X <= Integer'Last - N,
  Post => X = X'Old + N
is
begin
   for I in 1 .. N loop
      X := X + 1;
   end loop;
end Increment_Loop;
