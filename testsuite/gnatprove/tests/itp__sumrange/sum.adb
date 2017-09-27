
package body Sum with SPARK_Mode is

--   function Sum (A : Arr; I, J : Index) return Integer is
--     if J <= I then
--         return 0;
 --     else
--         return (A (I) + Sum (A, I + 1, J));
--      end if;
--   end Sum;

   function Simple_Sum (A : Arr; I, J : Index) return Integer is
      S : Integer := 0;
   begin
      for K in I .. J - 1 loop
         pragma Loop_Invariant (abs (S) <= K * 2000);
         pragma Loop_Invariant (S = Sum (A, I, K));
         S := S + A (K);
      end loop;
      return S;
   end Simple_Sum;

end Sum;
