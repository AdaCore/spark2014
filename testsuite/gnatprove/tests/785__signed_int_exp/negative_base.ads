package Negative_Base
  with SPARK_Mode
is

   --  Sign behaviour of exponentiation when the base is negative.

   subtype Small is Integer range -1_000 .. 1_000;
   subtype Tiny is Integer range -10 .. 10;

   function Neg_Square_Equals_Square (X : Small) return Boolean
   with Post => Neg_Square_Equals_Square'Result;

   function Neg_Cube_Is_Minus_Cube (X : Small) return Boolean
   with Post => Neg_Cube_Is_Minus_Cube'Result;

   --  General odd/even sign rule for a negated base raised to a run-time
   --  exponent: true for all N, but requires case analysis plus induction
   --  on N, which is out of reach for unaided SMT solvers.
   function Neg_Power_Sign (X : Tiny; N : Natural) return Boolean
   with Pre => N <= 12, Post => Neg_Power_Sign'Result;

end Negative_Base;
