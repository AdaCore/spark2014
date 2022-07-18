package body Test_Higher_Order3 with SPARK_Mode is

   procedure Prove_No_Overflows (A : Small_Matrix) is
      S : Integer := 0;
   begin
      if A'Length (2) = 0 then
         return;
      end if;
      for I in A'Range (1) loop
         pragma Loop_Invariant
           (if My_Sum_Int.No_Overflows (A, S, I, A'First (2))
            then My_Sum_Int.No_Overflows (A, 0, A'First (1), A'First (2)));
         pragma Loop_Invariant
           (S in (I - A'First (1)) * A'Length (2) * My_Small'First ..
            (I - A'First (1)) * A'Length (2) * My_Small'Last);
         for J in A'Range (2) loop
            pragma Loop_Invariant
              (if My_Sum_Int.No_Overflows (A, S, I, J)
               then My_Sum_Int.No_Overflows (A, 0, A'First (1), A'First (2)));
            pragma Loop_Invariant
              (S in ((I - A'First (1)) * A'Length (2) + (J - A'First (2)))
                  * My_Small'First ..
               ((I - A'First (1)) * A'Length (2) + (J - A'First (2)))
                  * My_Small'Last);
            S := S + Value (A (I, J));
         end loop;
      end loop;
   end;

   function Sum_Int (A : Small_Matrix) return Integer is
   begin
      Prove_No_Overflows (A);
      return My_Sum_Int.Sum (A);
   end Sum_Int;

end Test_Higher_Order3;
