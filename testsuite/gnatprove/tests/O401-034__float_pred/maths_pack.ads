with Types; use Types;

package Maths_Pack
  with SPARK_Mode
is
   --  Constants

   PI : constant :=
          3.14159_26535_89793_23846_26433_83279_50288_41971_69399_37511;

   --  Types

   --  Angle range type, in radians.
   subtype T_Radians is Float range -2.0 * PI .. 2.0 * PI;

   --  Procedures and functions

   --  Fast inverse square root
   --  See: http://en.wikipedia.org/wiki/Fast_inverse_square_root
   function Inv_Sqrt (X : Float) return Float
     with
       Pre  => X >= Float'Succ (0.0),
       Post => Inv_Sqrt'Result > 0.0 and Inv_Sqrt'Result < 2.0E+20;

   --  Imported atan2f function from C
   function Atan_2 (X : Float; Y : Float) return T_Radians
     with Global => null;
   pragma Import (C, Atan_2, "atan2f");


   --  Imported asin function from C
   function Asin (X : Float) return T_Radians
     with Global => null;
   pragma Import (C, Asin, "asinf");

end Maths_Pack;
