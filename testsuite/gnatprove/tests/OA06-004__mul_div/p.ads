package P
  with SPARK_Mode => On
is

   subtype LLI is Long_Long_Integer;

   type Uint_64 is mod 2 ** 64;
   --  Type used to represent intermediate results of arithmetic operations

   function Hi (X : Uint_64) return LLI is
      (LLI (X / 2 ** 32)) with Ghost;

   function Lo (X : Uint_64) return LLI is
      (LLI (X rem 2 ** 32)) with Ghost;
   --  Contract utility functions needed to cast Uint_64 to arbitrary precision
   --  integers within a single expression.

   function Mul_Div (V : Uint_64; M : Natural; D : Natural) return Uint_64 with
      Pre => D /= 0 and then
             (Hi (V) * (2 ** 32) + Lo (V)) * LLI (M) <= ((2 ** 63) - 1) * LLI (D);
   --  Compute V * M / D. Constraint_Error is raised in case of overflow,
   --  results above (2 ** 63) - 1 are considered as overflow. Therefore,
   --  the result can safely be converted to a signed 64-bit value.

end;
