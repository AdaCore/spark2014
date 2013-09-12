package Pck is pragma SPARK_Mode (On);
   type Uint_64 is range 0 .. 2 ** 63 - 1;
   type Int64 is range 0 .. 2 ** 63 - 1;
   function Mul_Div (V : Uint_64; M : Natural; D : Natural) return Uint_64 with
     Pre  => V <= 2 ** 63 - 1,
     Post => Int64 (Mul_Div'Result) = Int64 (V) * Int64 (M) / Int64 (D);
end Pck;
