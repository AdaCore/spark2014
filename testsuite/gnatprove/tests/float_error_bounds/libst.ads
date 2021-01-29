package Libst with SPARK_Mode is
   Max_Exact_Integer_Computation : constant := 2.0 ** 23;
   --  Upper bound of the interval on which integer computations are exact
   Float_Sqrt : constant Float := 2.0 ** 63;
   --  Safe bound for multiplication

   Max_Index : constant := 100;
   --  Number of elements in an array of values
   subtype Extended_Index is Natural range 0 .. Max_Index;
   subtype Index is Positive range 1 .. Max_Index;

   Max_Value : constant :=
     Float'Floor (Max_Exact_Integer_Computation / Float (Max_Index));
   --  Biggest integer value for which the sum is garanteed to be exact
   subtype Value is Float range -Max_Value .. Max_Value;
   type Value_Array is array (Index) of Value;

   Min_Weight : constant := 1.0 / Float_Sqrt;
   --  Avoid values too close to zero to prevent overflow on divisions
   subtype Weight is Float range 0.0 .. 1.0 with
     Predicate => Weight in 0.0 | Min_Weight .. 1.0;
   type Weight_Array is array (Index) of Weight;

   --  Definition of the weighted sum on an array of values using floating
   --  point computation.

   subtype Sum_Of_Weights is Float range 0.0 .. Float (Max_Index) with
     Predicate => Sum_Of_Weights in 0.0 | Min_Weight .. Float (Max_Index);
   function Sum_Weight_Rec
     (Weights : Weight_Array;
      I       : Extended_Index) return Float
   with
     Subprogram_Variant => (Decreases => I),
     Post => Sum_Weight_Rec'Result =
         (if I = 0 then 0.0 else Sum_Weight_Rec (Weights, I - 1) + Weights (I))
       and then Sum_Weight_Rec'Result in 0.0 |  Min_Weight .. Float (I);
   function Sum_Weight (Weights : Weight_Array) return Sum_Of_Weights is
     (Sum_Weight_Rec (Weights, Max_Index));
   --  Sum of an array of weights

   Max_Sum_Of_Values : constant := Max_Value * Float (Max_Index) / Min_Weight;
   subtype Sum_Of_Values is Float range -Max_Sum_Of_Values .. Max_Sum_Of_Values;
   function Weighted_Sum_Rec
     (Weights : Weight_Array;
      Values  : Value_Array;
      I       : Extended_Index) return Float
   with
     Subprogram_Variant => (Decreases => I),
     Post => Weighted_Sum_Rec'Result =
         (if I = 0 then 0.0
          else Weighted_Sum_Rec (Weights, Values, I - 1) + Weights (I) * Values (I))
       and then Weighted_Sum_Rec'Result in
             -(Max_Value * Float (I)) .. Max_Value * Float (I);
   function Weighted_Sum
     (Weights : Weight_Array;
      Values  : Value_Array) return Sum_Of_Values
   is
     (Weighted_Sum_Rec (Weights, Values, Max_Index) / Sum_Weight (Weights))
   with Pre => Sum_Weight (Weights) /= 0.0;
   --  Weighted sum of an array of values
end Libst;
