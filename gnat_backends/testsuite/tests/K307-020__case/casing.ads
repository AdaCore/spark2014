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
end Casing;
