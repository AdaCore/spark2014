with Ada.Numerics.Elementary_Functions;

package body Formal.Numerics.Elementary_Functions with
  SPARK_Mode => Off
is

   function Sqrt
     (X : Float)
      return Float
   renames Ada.Numerics.Elementary_Functions.Sqrt;

   function Log
     (X : Float)
      return Float
   renames Ada.Numerics.Elementary_Functions.Log;

   function Log
     (X, Base : Float)
      return Float
   renames Ada.Numerics.Elementary_Functions.Log;

   function Exp
     (X : Float)
      return Float
   renames Ada.Numerics.Elementary_Functions.Exp;

   function "**"
     (Left, Right : Float)
      return Float
   renames Ada.Numerics.Elementary_Functions."**";

   function Sin
     (X : Float)
      return Float
   renames Ada.Numerics.Elementary_Functions.Sin;

   function Sin
     (X, Cycle : Float)
      return Float
   renames Ada.Numerics.Elementary_Functions.Sin;

   function Cos
     (X : Float)
      return Float
   renames Ada.Numerics.Elementary_Functions.Cos;

   function Cos
     (X, Cycle : Float)
      return Float
   renames Ada.Numerics.Elementary_Functions.Cos;

   function Tan
     (X : Float)
      return Float
   renames Ada.Numerics.Elementary_Functions.Tan;

   function Tan
     (X, Cycle : Float)
      return Float
   renames Ada.Numerics.Elementary_Functions.Tan;

   function Cot
     (X : Float)
      return Float
   renames Ada.Numerics.Elementary_Functions.Cot;

   function Cot
     (X, Cycle : Float)
      return Float
   renames Ada.Numerics.Elementary_Functions.Cot;

   function Arcsin
     (X : Float)
      return Float
   renames Ada.Numerics.Elementary_Functions.Arcsin;

   function Arcsin
     (X, Cycle : Float)
      return Float
   renames Ada.Numerics.Elementary_Functions.Arcsin;

   function Arccos
     (X : Float)
      return Float
   renames Ada.Numerics.Elementary_Functions.Arccos;

   function Arccos
     (X, Cycle : Float)
      return Float
   renames Ada.Numerics.Elementary_Functions.Arccos;

   function Arctan
     (Y : Float;
      X : Float := 1.0)
      return Float
   renames Ada.Numerics.Elementary_Functions.Arctan;

   function Arctan
     (Y     : Float;
      X     : Float := 1.0;
      Cycle : Float)
      return Float
   renames Ada.Numerics.Elementary_Functions.Arctan;

   function Arccot
     (X   : Float;
      Y   : Float := 1.0)
      return Float
   renames Ada.Numerics.Elementary_Functions.Arccot;

   function Arccot
     (X     : Float;
      Y     : Float := 1.0;
      Cycle : Float)
      return Float
   renames Ada.Numerics.Elementary_Functions.Arccot;

   function Sinh
     (X : Float)
      return Float
   renames Ada.Numerics.Elementary_Functions.Sinh;

   function Cosh
     (X : Float)
      return Float
   renames Ada.Numerics.Elementary_Functions.Cosh;

   function Tanh
     (X : Float)
      return Float
   renames Ada.Numerics.Elementary_Functions.Tanh;

   function Coth
     (X : Float)
      return Float
   renames Ada.Numerics.Elementary_Functions.Coth;

   function Arcsinh
     (X : Float)
      return Float
   renames Ada.Numerics.Elementary_Functions.Arcsinh;

   function Arccosh
     (X : Float)
      return Float
   renames Ada.Numerics.Elementary_Functions.Arccosh;

   function Arctanh
     (X : Float)
      return Float
   renames Ada.Numerics.Elementary_Functions.Arctanh;

   function Arccoth
     (X : Float)
      return Float
   renames Ada.Numerics.Elementary_Functions.Arccoth;

end Formal.Numerics.Elementary_Functions;
