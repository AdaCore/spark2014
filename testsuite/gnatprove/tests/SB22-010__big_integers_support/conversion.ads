with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;
with Types; use Types;

package Conversion with
  SPARK_Mode
is
   pragma Annotate (GNATprove, Terminating, Conversion);

   function Partial_Conversion_Rec
     (X    : Integer_Curve25519;
      L    : Extended_Index_Type)
      return Big_Integer
   is
     (if L = 0 then (+X (0)) * Conversion_Array (0)
      else
         Partial_Conversion_Rec (X, L - 1) + (+X (L)) * Conversion_Array (L))
       with
         Pre  => X'First = 0 and then X'Length > 0 and then L in X'Range;

   function Partial_Conversion
     (X : Integer_Curve25519 ;
      L : Extended_Index_Type)
      return Big_Integer
   is
     (if L = -1 then Zero else Partial_Conversion_Rec (X, L))
       with
         Pre  => X'First = 0 and then L in X'Range;

   function To_Integer_255 (X : Integer_255) return Big_Integer is
     (Partial_Conversion (X, 9));

end Conversion;
