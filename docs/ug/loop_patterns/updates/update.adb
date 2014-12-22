package body Update
  with SPARK_Mode
is

   procedure Array_Update (A : in out Arr_T;
                           First_Idx, Last_Idx: in Index_T;
                           New_Val : in Component_T)
   is
   begin

      for Idx in First_Idx .. Last_Idx loop
         A (Idx) := New_Val;
         pragma Loop_Invariant
           (for all J in First_Idx .. Idx => A (J) = New_Val);
      end loop;

   end Array_Update;

end Update;
