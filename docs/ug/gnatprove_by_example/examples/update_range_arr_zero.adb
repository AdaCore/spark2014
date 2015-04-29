with Loop_Types; use Loop_Types;

procedure Update_Range_Arr_Zero (A : in out Arr_T; First, Last : Index_T) with
  SPARK_Mode,
  Post => A = A'Old'Update (First .. Last => 0)
is
   A_Old : constant Arr_T := A; --  HACK should use A'Loop_Entry'Update
begin
   for J in First .. Last loop
      A(J) := 0;
      pragma Loop_Invariant (A = A_Old'Update (First .. J => 0));
   end loop;
end Update_Range_Arr_Zero;
