package body Assert_Loop_05
is
   function Value_Present (A: A_Type; X : Integer) return Boolean
   is
      I : Index := Index'First;
   begin
      while A (I) /= X and I < Index'Last loop
         --# assert I < Index'Last and
         --#        (for all M in Index range Index'First .. I => (A (M) /= X));
         I := I + 1;
      end loop;
      return A (I) = X;
   end Value_Present;
end Assert_Loop_05;
