package Mul_Div_2
  with SPARK_Mode => On
is

   subtype LLI is Long_Long_Integer;

   function Mul_Div (V : LLI; M : Natural; D : Positive) return LLI with
     Pre => (if V >= 0
             then (V * LLI (M) + LLI (D) / 2) / LLI (D) <= LLI'Last
             else -(((-V) * LLI (M) + LLI (D) / 2) / LLI (D)) >= LLI'First),
     Post => Mul_Div'Result =
             (if V >= 0
              then (V * LLI (M) + LLI (D) / 2) / LLI (D)
              else -(((-V) * LLI (M) + LLI (D) / 2) / LLI (D)));

end;
