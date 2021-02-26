with Ada.Numerics.Big_Numbers.Big_Reals; use Ada.Numerics.Big_Numbers.Big_Reals;
with Sqrt_Spec; use Sqrt_Spec;

package Norm.Reals with SPARK_Mode, Ghost is
   package Float_Conversions is new
     Ada.Numerics.Big_Numbers.Big_Reals.Float_Conversions (Float);
   use Float_Conversions;
   --  Conversions between Big_Real and Float

   --  Definition of Norm using exact real computation

   function Sum_Of_Squares_Rec
     (Values : Value_Array;
      I      : Extended_Index) return Valid_Big_Real
   with Subprogram_Variant => (Decreases => I),
     Post => Sum_Of_Squares_Rec'Result >= 0.0;

   function Sum_Of_Squares_Rec
     (Values : Value_Array;
      I      : Extended_Index) return Valid_Big_Real
   is
     (if I = 0 then Big_Real'(0.0)
      else Sum_Of_Squares_Rec (Values, I - 1)
        + To_Big_Real (Values (I)) * To_Big_Real (Values (I)));

   function Norm (Values : Value_Array) return Valid_Big_Real is
     (Sqrt (Sum_Of_Squares_Rec (Values, Max_Index)));
end Norm.Reals;
