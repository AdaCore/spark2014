with Ada.Numerics;

package body Foo is

   type Float64 is digits 15;

   subtype Angle_T is Float64 range -360.0 .. 360.0;

   Degrees_Per_Rad : constant := 180.0 / Ada.Numerics.Pi;

   function Foobar (X : Integer) return Angle_T
   is (Angle_T (Float64 (X) * (2.0 ** (-29)) * Degrees_Per_Rad));

end Foo;
