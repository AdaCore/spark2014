with Loop_Types; use Loop_Types; use Loop_Types.Vectors;

procedure Validate_Vec_Zero (V : Vec_T; Success : out Boolean) with
  SPARK_Mode,
  Post => Success = (for all J in First_Index (V) .. Last_Index (V) => Element (V, J) = 0)
is
begin
   for J in First_Index (V) .. Last_Index (V) loop
      if Element (V, J) /= 0 then
         Success := False;
         return;
      end if;
      pragma Loop_Invariant (for all K in First_Index (V) .. J => Element (V, K) = 0);
   end loop;

   Success := True;
end Validate_Vec_Zero;
