package Casing is
   type En is (A, B, C, D, E);

   function F (X : En) return Integer
      with Post =>
         (F'Result =
            (case X is
               when A => 0,
               when B => 1,
               when C | D => 2,
               when others => 3));

   type Two is (M, N);

   function G (X : Two) return Integer
      with Post =>
         (G'Result =
            (case X is
               when M => 0,
               when N => 1));
end Casing;
