with Loop_Types; use Loop_Types;
package Update
  with SPARK_Mode
is

   procedure Array_Update (A : in out Arr_T;
                           First_Idx, Last_Idx: in Index_T;
                           New_Val : in Component_T) with
     Post =>  A = A'Old'Update (First_Idx .. Last_Idx => New_Val);

end Update;
