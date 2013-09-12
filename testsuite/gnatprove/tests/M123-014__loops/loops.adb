procedure Loops is 
   Count : Integer;
begin
   for I in 1 .. 5 loop
      Count := 0;
      for K in 1 .. I loop
         Count := Count + 1;
         pragma Loop_Invariant (Count = K);
      end loop;
      pragma Loop_Invariant (Count = I);
   end loop;
end Loops;
