package body Assert_Loop_14
  with SPARK_Mode
is
   function Value_Present (A : A_Type; X : Integer) return Boolean is
      I : Index := Index'First;
   begin
      while A (I) /= X and I < Index'Last loop
         pragma Loop_Invariant
           (I < Index'Last
            and (for all M in Index'First .. I => A (M) /= X));
         I := I + 1;
      end loop;

      return A (I) = X;
   end Value_Present;
end Assert_Loop_14;
