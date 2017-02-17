procedure Loops is
   Count : Integer := 0;
begin
   for I in 1 .. 5 loop
      pragma Loop_Invariant (Count = I - 1);
      Count := 0;
      for K in 1 .. I loop
         Count := Count + 1;
         pragma Loop_Invariant (Count = K);
      end loop;
   end loop;
end Loops;
