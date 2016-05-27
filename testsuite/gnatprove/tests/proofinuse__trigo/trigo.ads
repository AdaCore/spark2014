package Trigo with
  SPARK_Mode
is
   function Pow2 (X : Float) return Float is (X * X);
   function Pow3 (X : Float) return Float is (X * X * X);
   function Pow4 (X : Float) return Float is (X * X * X * X);
   function Pow5 (X : Float) return Float is (X * X * X * X * X);
   function Pow6 (X : Float) return Float is (X * X * X * X * X * X);
   function Pow7 (X : Float) return Float is (X * X * X * X * X * X * X);
   function Pow8 (X : Float) return Float is (X * X * X * X * X * X * X * X);
   function Pow9 (X : Float) return Float is (X * X * X * X * X * X * X * X * X);

   function Approx_Sin (X : Float) return Float is
      (X - Pow3 (X) / 6.0 + Pow5 (X) / 120.0 - Pow7 (X) / 5040.0);

   function Sin (X : Float) return Float with
     Pre  => X in -1.0 .. 1.0,
     Post => abs (Sin'Result - Approx_Sin (X)) < 0.000003;

   function Approx_Cos (X : Float) return Float is
      (1.0 - Pow2 (X) / 2.0 + Pow4 (X) / 24.0 - Pow6 (X) / 720.0 + Pow8 (X) / 40_320.0);

   function Cos (X : Float) return Float with
     Pre  => X in -1.0 .. 1.0,
     Post => abs (Cos'Result - Approx_Cos (X)) < 0.000003;

   function Approx_Tan (X : Float) return Float is
      (X + Pow3 (X) / 3.0 + 2.0 * Pow5 (X) / 15.0 + 17.0 * Pow7 (X) / 315.0 + 62.0 * Pow9 (X) / 2835.0);

   function Tan (X : Float) return Float with
     Pre  => X in -0.5 .. 0.5,
     Post => abs (Tan'Result - Approx_Tan (X)) < 0.0001;

end Trigo;
