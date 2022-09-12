with SPARK.Lemmas.Integer_Arithmetic; use SPARK.Lemmas.Integer_Arithmetic;

package body Math with
  SPARK_Mode
is
   procedure Apply_Ratio (V : in out Sorted_Values; Num, Denom : Value) is
      Prev_Value : Value := 0 with Ghost;
   begin
      for J in Index loop
         Lemma_Mult_Scale (Val         => V(J),
                           Scale_Num   => Num,
                           Scale_Denom => Denom,
                           Res         => V(J) * Num / Denom);
         Lemma_Mult_Is_Monotonic (Val1   => Prev_Value,
                                  Val2   => V(J),
                                  Factor => Num);
         Lemma_Div_Is_Monotonic (Val1  => Prev_Value * Num,
                                 Val2  => V(J) * Num,
                                 Denom => Denom);
         pragma Assert (if J > Index'First then
                          V(J - 1) <= V(J) * Num / Denom);

         Prev_Value := V(J);
         V(J) := V(J) * Num / Denom;

         pragma Loop_Invariant (Sorted (V));
         pragma Loop_Invariant (Prev_Value = V'Loop_Entry(J));
         pragma Loop_Invariant
           (for all K in Index'First .. J => V(K) = V'Loop_Entry(K) * Num / Denom);
         pragma Loop_Invariant
           (for all K in J + 1 .. Index'Last => V(K) = V'Loop_Entry(K));
      end loop;
   end Apply_Ratio;

end Math;
