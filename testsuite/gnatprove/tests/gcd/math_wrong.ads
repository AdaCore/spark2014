package Math_Wrong is

   function Divides (A, B : in Positive) return Boolean is (B mod A = 0) with Ghost;

   function GCD (A, B : in Positive) return Positive with
     Post => Divides (GCD'Result, A)
       and then Divides (GCD'Result, B);

end Math_Wrong;
