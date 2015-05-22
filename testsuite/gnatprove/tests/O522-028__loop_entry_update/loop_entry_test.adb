with Loop_Types; use Loop_Types;

package body Loop_Entry_Test
  with SPARK_Mode
is

   procedure Update_Range_Arr_Zero (A : in out Arr_T; First, Last : Index_T) is
   begin
      for J in First .. Last loop
         A(J) := 0;
         --pragma Loop_Invariant (A = A'Loop_Entry'Update (First .. J => 0));
      end loop;
   end Update_Range_Arr_Zero;

   procedure Update_Range_Arr_Zero_With_Tmp (A : in out Arr_T; First, Last : Index_T) is
      A_Loop_Entry : Arr_T;
   begin
      A_Loop_Entry := A;
      for J in First .. Last loop
         A(J) := 0;
         pragma Loop_Invariant (A = A_Loop_Entry'Update (First .. J => 0));
      end loop;
   end Update_Range_Arr_Zero_With_Tmp;

end Loop_Entry_Test;
