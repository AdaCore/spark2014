with Loop_Types; use Loop_Types;

procedure Update_Range_Arr_Zero (A : in out Arr_T; First, Last : Index_T) with
  SPARK_Mode,
  Post => A = A'Old'Update (First .. Last => 0)
is
begin
   for J in First .. Last loop
      A(J) := 0;
      pragma Loop_Invariant (A = A'Loop_Entry'Update (First .. J => 0));
   end loop;
end Update_Range_Arr_Zero;
