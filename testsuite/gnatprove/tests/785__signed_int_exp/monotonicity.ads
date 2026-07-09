package Monotonicity
  with SPARK_Mode
is

   --  Monotonicity properties of exponentiation. All are true, but their
   --  proofs are inherently inductive on the exponent, so these are
   --  expected to be some of the hardest checks in this test for
   --  automatic provers.

   subtype Small_Exp is Natural range 0 .. 20;

   function Strictly_Increasing_In_Exponent
     (X : Integer; N1, N2 : Small_Exp) return Boolean
   with
     Pre  => X > 1 and then N1 < N2,
     Post => Strictly_Increasing_In_Exponent'Result;

   function Nondecreasing_In_Exponent
     (X : Integer; N1, N2 : Small_Exp) return Boolean
   with
     Pre  => X >= 1 and then N1 <= N2,
     Post => Nondecreasing_In_Exponent'Result;

   subtype Small_Base is Natural range 0 .. 20;

   function Nondecreasing_In_Base
     (X1, X2 : Small_Base; N : Positive) return Boolean
   with Pre => X1 <= X2 and then N <= 20, Post => Nondecreasing_In_Base'Result;

end Monotonicity;
