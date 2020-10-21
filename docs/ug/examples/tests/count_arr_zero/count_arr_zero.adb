with Loop_Types; use Loop_Types;

procedure Count_Arr_Zero (A : Arr_T; Counter : out Natural) with
  SPARK_Mode,
  Post => (Counter in 0 .. A'Length) and then
          ((Counter = 0) = (for all K in A'Range => A(K) /= 0))
is
begin
   Counter := 0;

   for J in A'Range loop
      if A(J) = 0 then
         Counter := Counter + 1;
      end if;
      pragma Loop_Invariant (Counter in 0 .. J);
      pragma Loop_Invariant ((Counter = 0) = (for all K in A'First .. J => A(K) /= 0));
   end loop;
end Count_Arr_Zero;
