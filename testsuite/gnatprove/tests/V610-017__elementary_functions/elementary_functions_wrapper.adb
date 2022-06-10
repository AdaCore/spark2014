with Ada.Numerics.Elementary_Functions;

package body Elementary_Functions_Wrapper with SPARK_Mode is
   package EF renames Ada.Numerics.Elementary_Functions;

   function Sqrt (X : Float) return Float is (EF.Sqrt (X));

   function Log (X : Float) return Float is (EF.Log (X));

   function Log (X, Base : Float) return Float is (EF.Log (X, Base));

   function Exp (X : Float) return Float is (EF.Exp (X)); --@OVERFLOW_CHECK:FAIL

   function "**" (Left, Right : Float) return Float is (EF."**" (Left, Right));--@OVERFLOW_CHECK:FAIL

   function Sin (X : Float) return Float is (EF.Sin (X));

   function Sin (X, Cycle : Float) return Float is (EF.Sin (X, Cycle));

   function Cos (X : Float) return Float is (EF.Cos (X));

   function Cos (X, Cycle : Float) return Float is (EF.Cos (X, Cycle));

   function Tan (X : Float) return Float is (EF.Tan (X));

   function Tan (X, Cycle : Float) return Float is (EF.Tan (X, Cycle));--@PRECONDITION:FAIL

   function Cot (X : Float) return Float is (EF.Cot (X));--@OVERFLOW_CHECK:FAIL

   function Cot (X, Cycle : Float) return Float is (EF.Cot (X, Cycle));--@OVERFLOW_CHECK:FAIL

   function Arcsin (X : Float) return Float is (EF.Arcsin (X));

   function Arcsin (X, Cycle : Float) return Float is (EF.Arcsin (X, Cycle));

   function Arccos (X : Float) return Float is (EF.Arccos (X));

   function Arccos (X, Cycle : Float) return Float is (EF.Arccos (X, Cycle));

   function Arctan
     (Y : Float;
      X : Float := 1.0) return Float is (EF.Arctan (Y, X));

   function Arctan
     (Y     : Float;
      X     : Float := 1.0;
      Cycle : Float) return Float is (EF.Arctan (Y, X, Cycle));

   function Arccot
     (X   : Float;
      Y   : Float := 1.0) return Float is (EF.Arccot (X, Y));

   function Arccot
     (X     : Float;
      Y     : Float := 1.0;
      Cycle : Float) return Float is (EF.Arccot (X, Y, Cycle));

   function Sinh (X : Float) return Float is (EF.Sinh (X));--@OVERFLOW_CHECK:FAIL

   function Cosh (X : Float) return Float is (EF.Cosh (X));--@OVERFLOW_CHECK:FAIL

   function Tanh (X : Float) return Float is (EF.Tanh (X));

   function Coth (X : Float) return Float  is (EF.Coth (X));--@OVERFLOW_CHECK:FAIL

   function Arcsinh (X : Float) return Float is (EF.Arcsinh (X));

   function Arccosh (X : Float) return Float is (EF.Arccosh (X));

   function Arctanh (X : Float) return Float is (EF.Arctanh (X));--@OVERFLOW_CHECK:FAIL

   function Arccoth (X : Float) return Float is (EF.Arccoth (X));--@OVERFLOW_CHECK:FAIL

end Elementary_Functions_Wrapper;
