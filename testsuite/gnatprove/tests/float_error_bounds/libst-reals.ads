with Ada.Numerics.Big_Numbers.Big_Reals; use Ada.Numerics.Big_Numbers.Big_Reals;

package Libst.Reals with
  SPARK_Mode,
  Ghost
is
   package Float_Conversions is new
     Ada.Numerics.Big_Numbers.Big_Reals.Float_Conversions (Float);
   use Float_Conversions;
   --  Conversions between Big_Real and Float

   --  Definition of the weighted sum on an array of values using exact real
   --  computation.

   function Sum_Weight_Rec
     (Weights : Weight_Array;
      I       : Extended_Index) return Valid_Big_Real
   is
     (if I = 0 then Valid_Big_Real'(0.0)
      else Sum_Weight_Rec (Weights, I - 1) + To_Big_Real (Weights (I)))
   with Subprogram_Variant => (Decreases => I),
     Post => Sum_Weight_Rec'Result >= 0.0;
   function Sum_Weight (Weights : Weight_Array) return Valid_Big_Real is
     (Sum_Weight_Rec (Weights, Max_Index));
   --  Sum of an array of weights

   function Weighted_Sum_Rec
     (Weights : Weight_Array;
      Values  : Value_Array;
      I       : Extended_Index) return Valid_Big_Real
   is
     (if I = 0 then Valid_Big_Real'(0.0)
      else Weighted_Sum_Rec (Weights, Values, I - 1)
        + To_Big_Real (Weights (I)) * To_Big_Real (Values (I)))
   with Subprogram_Variant => (Decreases => I);
   function Weighted_Sum
     (Weights : Weight_Array;
      Values  : Value_Array) return Valid_Big_Real
   is
     (Weighted_Sum_Rec (Weights, Values, Max_Index) / Sum_Weight (Weights))
   with Pre => Sum_Weight (Weights) /= Valid_Big_Real'(0.0);
   --  Weighted sum of an array of values
end Libst.Reals;
