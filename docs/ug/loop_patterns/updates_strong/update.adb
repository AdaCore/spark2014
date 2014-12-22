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
           ((for all J in First_Idx .. Idx => A (J) = New_Val) and
              (for all K in A'First .. First_Idx - 1 =>
                 A (K) = A'Loop_Entry (K)) and
              (for all K in Last_Idx + 1 .. A'Last => A (K) = A'Loop_Entry (K)));
      end loop;

   end Array_Update;

end Update;
