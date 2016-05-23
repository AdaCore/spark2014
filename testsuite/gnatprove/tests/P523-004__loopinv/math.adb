package body Math with
  SPARK_Mode
is
   procedure Shift_Right (V : in out Sorted_Values) is
      Prev_Value : Value := V(Index'First);
      Tmp_Value  : Value;
   begin
      for J in Index loop
         Tmp_Value := Prev_Value;
         Prev_Value := V(J);
         V(J) := Tmp_Value;

         pragma Loop_Invariant (Prev_Value = V'Loop_Entry(J));
         pragma Loop_Invariant
           (for all K in Index'First .. J => V(K) = V'Loop_Entry(Index'Max(Index'First, K - 1)));
         pragma Loop_Invariant
           (for all K in J + 1 .. Index'Last => V(K) = V'Loop_Entry(K));
      end loop;
   end Shift_Right;

end Math;
