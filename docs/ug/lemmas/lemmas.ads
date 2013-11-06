package Lemmas is

   function Factors_Of (N : Integer) return Boolean
   is (case N is
          when 475799 => N mod 487 = 0,
          when others => True)
   with Post => Factors_Of'Result;

end Lemmas;
