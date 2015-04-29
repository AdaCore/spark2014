with Loop_Types; use Loop_Types; use Loop_Types.Vectors;

procedure Update_Range_Vec_Zero (V : in out Vec_T; First, Last : Index_T) with
  SPARK_Mode,
  Pre  => Last <= Last_Index (V),
  Post => (for all J in First .. Last => Element (V, J) = 0)
is
begin
   for J in First .. Last loop
      Replace_Element (V, J, 0);
      pragma Loop_Invariant (Last_Index (V) = Last_Index (V)'Loop_Entry);
      pragma Loop_Invariant (for all K in First .. J => Element (V, K) = 0);
   end loop;
end Update_Range_Vec_Zero;
