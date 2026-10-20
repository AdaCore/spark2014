procedure Nested_Invariant (N : Natural; X : out Natural) with
  SPARK_Mode,
  Post => X = N
is
begin
   X := 0;
   while X < N loop
      begin
         begin
            pragma Loop_Invariant (X <= N);
         end;
      end;
      X := X + 1;
   end loop;
end Nested_Invariant;
