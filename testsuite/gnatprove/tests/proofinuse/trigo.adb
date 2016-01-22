with Ada.Numerics.Elementary_Functions;

package body Trigo with
  SPARK_Mode
is
   function Sin (X : Float) return Float is
      (Ada.Numerics.Elementary_Functions.Sin (X));

   function Cos (X : Float) return Float is
      (Ada.Numerics.Elementary_Functions.Cos (X));

   function Tan (X : Float) return Float is
      (Ada.Numerics.Elementary_Functions.Tan (X));

end Trigo;
