with Loop_Types; use Loop_Types; use Loop_Types.Vectors;

procedure Update_Vec_Zero (V : in out Vec_T; Threshold : Component_T) with
  SPARK_Mode,
  Post => (for all J in First_Index (V) .. Last_Index (V) => Element (V, J) not in 1 .. Threshold)
is
begin
   for J in First_Index (V) .. Last_Index (V) loop
      if Element (V, J) <= Threshold then
         Replace_Element (V, J, 0);
      end if;
      pragma Loop_Invariant (Last_Index (V) = Last_Index (V)'Loop_Entry);
      pragma Loop_Invariant (for all K in First_Index (V) .. J => Element (V, K) not in 1 .. Threshold);
   end loop;
end Update_Vec_Zero;
