with Loop_Types; use Loop_Types; use Loop_Types.Vectors;

procedure Count_Vec_Zero (V : Vec_T; Counter : out Natural) with
  SPARK_Mode,
  Post => (Counter in 0 .. Natural (Length (V))) and then
          ((Counter = 0) = (for all K in First_Index (V) .. Last_Index (V) => Element (V, K) /= 0))
is
begin
   Counter := 0;

   for J in First_Index (V) .. Last_Index (V) loop
      if Element (V, J) = 0 then
         Counter := Counter + 1;
      end if;
      pragma Loop_Invariant (Counter in 0 .. J);
      pragma Loop_Invariant ((Counter = 0) = (for all K in First_Index (V) .. J => Element (V, K) /= 0));
   end loop;
end Count_Vec_Zero;
