package Norm.Reals.Errors with SPARK_Mode, Ghost is

   procedure Error_For_Sum_Rec
     (Values : Value_Array;
      I      : Index)
   with Subprogram_Variant => (Decreases => I),
     Post =>
       abs (To_Big_Real (Sum_Of_Squares_Rec (Values, I)) -
              Sum_Of_Squares_Rec (Values, I))
         <=  2.5E-45 * To_Real (I) + (1.0E-7 + 1.01E-7 * To_Real (I - 1))
           * Sum_Of_Squares_Rec (Values, I);
   --  Error bound on the computation of Sum_Of_Squares_Rec

   procedure Norm (Values : Value_Array) with
     Post =>
       abs (To_Big_Real (Norm (Values)) - Norm (Values))
         <=  5.1E-22 + 5.3E-6 * Norm (Values);
   --  Error bound on the computation of Norm

end Norm.Reals.Errors;
