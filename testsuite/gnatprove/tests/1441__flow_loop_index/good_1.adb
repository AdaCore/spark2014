function Good_1 (A : String) return Integer
  with Depends => (Good_1'Result => A), Ghost
is
begin
   for E of A loop
      return E'Loop_Index;
   end loop;
   --  do not care about null array
   return 0;
end;
