package Math_Simple_Abstract is

   function Divides (A, B : in Positive) return Boolean is
     (for some C in Positive => A * C = B)
   with Ghost;

   function GCD (A, B : in Positive) return Positive with
     Post => Divides (GCD'Result, A)
       and then Divides (GCD'Result, B)
       and then (for all X in GCD'Result + 1 .. Integer'Min (A, B) =>
                   not (Divides (X, A) and Divides (X, B)));

end Math_Simple_Abstract;
