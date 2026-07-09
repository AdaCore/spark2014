package Power_Of_Two
  with SPARK_Mode
is

   --  Properties specific to powers of two: a literal base of 2, which is
   --  the most common exponentiation pattern in real code (bit widths,
   --  buffer sizes, range bounds).

   subtype Exp_Range is Natural range 0 .. 30;

   function Two_Pow (N : Exp_Range) return Positive
   with Post => Two_Pow'Result = 2 ** N;

   function Two_Pow_Is_Positive (N : Exp_Range) return Boolean
   with Post => Two_Pow_Is_Positive'Result;

   function Two_Pow_Even_For_Positive_N (N : Exp_Range) return Boolean
   with Pre => N >= 1, Post => Two_Pow_Even_For_Positive_N'Result;

   function Two_Pow_Doubling (N : Natural) return Boolean
   with Pre => N < 30, Post => Two_Pow_Doubling'Result;

   function Two_Pow_Product (A, B : Natural) return Boolean
   with Pre => A <= 15 and then B <= 15, Post => Two_Pow_Product'Result;

   function Two_Pow_Strictly_Increasing (N1, N2 : Exp_Range) return Boolean
   with Pre => N1 < N2, Post => Two_Pow_Strictly_Increasing'Result;

   --  Sanity check that the literal bounds used throughout the test suite
   --  for 32-bit and 64-bit signed ranges do not themselves overflow.
   function Range_Bound_Constants return Boolean
   with Post => Range_Bound_Constants'Result;

end Power_Of_Two;
