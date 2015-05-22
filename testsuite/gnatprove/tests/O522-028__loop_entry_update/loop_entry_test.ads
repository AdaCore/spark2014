with Loop_Types; use Loop_Types;

package Loop_Entry_Test
  with SPARK_Mode
is

   procedure Update_Range_Arr_Zero (A : in out Arr_T; First, Last : Index_T) with
     Post => A = A'Old'Update (First .. Last => 0);

   procedure Update_Range_Arr_Zero_With_Tmp (A : in out Arr_T; First, Last : Index_T) with
     Post => A = A'Old'Update (First .. Last => 0);

end Loop_Entry_Test;
