with Ada.Numerics; use Ada.Numerics;

package Maths_Pack
  with SPARK_Mode
is

   --  Types

   --  Angle range type, in radians.
   subtype T_Radians is Float range -2.0 * Pi .. 2.0 * Pi;

   --  Procedures and functions

   --  Return the inverse square root using the sqrtf builtin
   function Inv_Sqrt (X : Float) return Float
     with
       Pre  => X >= Float'Succ (0.0),
       Post => Inv_Sqrt'Result > 0.0 and Inv_Sqrt'Result < 2.7E+22;

   --  Wrapper for Ada.Numerics.Elementary_Functions.Arctan
   function Atan (Y :  Float; X : Float) return T_Radians;

   --  Wrapper for Ada.Numerics.Elementary_Functions.Arctan
   function Asin (X : Float) return T_Radians;

end Maths_Pack;
