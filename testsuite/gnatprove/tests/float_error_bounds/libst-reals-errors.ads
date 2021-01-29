package Libst.Reals.Errors with SPARK_Mode is

   procedure Error_For_SW_Rec
     (Weights : Weight_Array;
      I       : Index)
   with Subprogram_Variant => (Decreases => I),
     Post =>
       abs (To_Big_Real (Sum_Weight_Rec (Weights, I)) -
              Sum_Weight_Rec (Weights, I))
         <= To_Real (I - 1) * 1.01E-7 * Sum_Weight_Rec (Weights, I);
   --  Error bound on the computation of Sum_Weight_Rec

   procedure Error_For_SW (Weights : Weight_Array)
   with Post =>
       abs (To_Big_Real (Sum_Weight (Weights)) - Sum_Weight (Weights))
         <= 1.0E-5 * Sum_Weight (Weights);
   --  Error bound on the computation of Sum_Weight

   function Weighted_Sum_Abs_Rec
     (Weights : Weight_Array;
      Values  : Value_Array;
      I       : Extended_Index) return Valid_Big_Real
   is
     (if I = 0 then Valid_Big_Real'(0.0)
      else Weighted_Sum_Abs_Rec (Weights, Values, I - 1)
      + To_Big_Real (Weights (I)) * abs (To_Big_Real (Values (I))))
   with Subprogram_Variant => (Decreases => I),
       Post => Weighted_Sum_Abs_Rec'Result >= 0.0;

   function Weighted_Sum_Abs
     (Weights : Weight_Array;
      Values  : Value_Array) return Valid_Big_Real
   is
     (Weighted_Sum_Abs_Rec (Weights, Values, Max_Index) / Sum_Weight (Weights))
   with Pre => Sum_Weight (Weights) /= Valid_Big_Real'(0.0);
   --  Weighted sum of the absolute values of elements of the Values array

   procedure Sum_Less_Than_Sum_Abs
     (Weights : Weight_Array;
      Values  : Value_Array;
      I       : Extended_Index)
   with Subprogram_Variant => (Decreases => I),
     Post => abs (Weighted_Sum_Rec (Weights, Values, I))
       <= Weighted_Sum_Abs_Rec (Weights, Values, I);
   --  The absolute value of the weighted sum is less than the weighted sum of
   --  the absolute values.

   procedure Bound_Sum_Abs
     (Weights : Weight_Array;
      Values  : Value_Array;
      I       : Extended_Index)
   with Subprogram_Variant => (Decreases => I),
     Post => Weighted_Sum_Abs_Rec (Weights, Values, I)
       <= Sum_Weight_Rec (Weights, I) * To_Big_Real (Max_Value);
   --  Bound the absolute value of the weighted sum

   procedure Error_For_Sum_Rec
     (Weights : Weight_Array;
      Values  : Value_Array;
      I       : Index)
   with Subprogram_Variant => (Decreases => I),
     Post =>
       abs (To_Big_Real (Weighted_Sum_Rec (Weights, Values, I)) -
              Weighted_Sum_Rec (Weights, Values, I))
         <= 2.5E-45 * To_Real (I) + (1.0E-7 + 1.01E-7 * To_Real (I - 1))
           * Weighted_Sum_Abs_Rec (Weights, Values, I);
   --  Error bound on the computation of Weighted_Sum_Rec

   procedure Error_For_Sum
     (Weights : Weight_Array;
      Values  : Value_Array)
   with
     Pre  => Sum_Weight (Weights) /= Valid_Big_Real'(0.0),
     Post =>
         abs (To_Big_Real (Weighted_Sum (Weights, Values)) -
                Weighted_Sum (Weights, Values))
           <= 1.25E-45 + 2.52E-43 / Sum_Weight (Weights)
            + 2.05E-5 * Weighted_Sum_Abs (Weights, Values);
   --  Error bound on the computation of Weighted_Sum

end Libst.Reals.Errors;
