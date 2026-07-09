package Fast_Exponentiation
  with SPARK_Mode
is

   --  Exponentiation-by-squaring on plain (bounded) signed integers,
   --  unlike the arbitrary-precision Big_Integer version used elsewhere
   --  in the test suite. Here every multiplication is also an overflow
   --  check, so the loop invariant must additionally carry enough
   --  information to rule out overflow at each step.

   subtype Base_Range is Natural range 0 .. 3;
   subtype Exp_Range is Natural range 0 .. 15;

   function Fast_Exp (X : Base_Range; N : Exp_Range) return Natural
   with Post => Fast_Exp'Result = X ** N;

   --  Recursive version of the same algorithm.
   function Fast_Exp_Recursive (X : Base_Range; N : Exp_Range) return Natural
   with
     Subprogram_Variant => (Decreases => N),
     Post               => Fast_Exp_Recursive'Result = X ** N;

end Fast_Exponentiation;
