package body Update_Illegal_2
  with SPARK_Mode
is
   type Multdim_Array_T is
     array (Integer range 1 .. 10, Integer range 1 .. 10) of Boolean;

   procedure P1 (Arr : in out Multdim_Array_T) is
   begin
      Arr := Arr'Update (1 => True);
      --  The length of each index_expression_list must be equal
      --  to the dimensionality of the multidimensional array.
   end P1;
end Update_Illegal_2;
