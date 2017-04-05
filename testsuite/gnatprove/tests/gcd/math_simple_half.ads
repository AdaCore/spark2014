package Math_Simple_Half is

   function Divides (A, B : in Positive) return Boolean is (B mod A = 0) with Ghost;

   function GCD (A, B : in Positive) return Positive with
     Post => Divides (GCD'Result, A)
       and then Divides (GCD'Result, B)
       and then (for all X in GCD'Result + 1 .. Integer'Min (A, B) =>
                   not (Divides (X, A) and Divides (X, B)));

end Math_Simple_Half;
