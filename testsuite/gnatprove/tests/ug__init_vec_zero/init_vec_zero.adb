with Loop_Types; use Loop_Types; use Loop_Types.Vectors;

procedure Init_Vec_Zero (V : in out Vec_T) with
  SPARK_Mode,
  Post => (for all J in First_Index (V) .. Last_Index (V) => Element (V, J) = 0)
is
begin
   for J in First_Index (V) .. Last_Index (V) loop
      Replace_Element (V, J, 0);
      pragma Loop_Invariant (Last_Index (V) = Last_Index (V)'Loop_Entry);
      pragma Loop_Invariant (for all K in First_Index (V) .. J => Element (V, K) = 0);
   end loop;
end Init_Vec_Zero;
