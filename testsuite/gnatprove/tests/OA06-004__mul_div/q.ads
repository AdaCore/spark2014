package Q
  with SPARK_Mode => On
is
   --  This variant of Mul_Div gets the first argument as a signed integer
   --  and thus has a straightforward contract.

   subtype LLI is Long_Long_Integer;

   type Uint_64 is mod 2 ** 64;
   --  Type used to represent intermediate results of arithmetic operations

   function Mul_Div (VS : LLI; M : Natural; D : Natural) return Uint_64 with
      Pre => D /= 0 and then
             abs (VS) * LLI (M) <= (2 ** 63 - 1) * LLI (D);
   --  Compute |VS| * M / D. Constraint_Error is raised in case of overflow,
   --  results above (2 ** 63) - 1 are considered as overflow. Therefore,
   --  the result can safely be converted to a signed 64-bit value.

end;
