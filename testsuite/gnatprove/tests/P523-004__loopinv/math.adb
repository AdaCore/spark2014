package body Math with
  SPARK_Mode
is
   procedure Shift_Right (V : in out Sorted_Values) is
   begin
      for J in Index loop
         V(J) := V(Index'Max(Index'First, J - 1));

         pragma Loop_Invariant
           (for all K in Index'First .. J => V(K) = V'Loop_Entry(Index'Max(Index'First, K - 1)));
         pragma Loop_Invariant
           (for all K in J + 1 .. Index'Last => V(K) = V'Loop_Entry(K));
      end loop;
   end Shift_Right;

end Math;
