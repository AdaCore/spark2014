with SPARK.Float_Arithmetic_Lemmas; use SPARK.Float_Arithmetic_Lemmas;

package body Libst with SPARK_Mode is

   function Sum_Weight_Rec
     (Weights : Weight_Array;
      I       : Extended_Index) return Float
   is
   begin
      if I = 0 then
         return 0.0;
      else
         Lemma_Add_Is_Monotonic (Sum_Weight_Rec (Weights, I - 1), Float (I - 1), Weights (I));
         Lemma_Integer_Add_Exact (Float (I - 1), 1.0, I - 1, 1);
         return Sum_Weight_Rec (Weights, I - 1) + Weights (I);
      end if;
   end Sum_Weight_Rec;

   function Sum_Weight (Weights : Weight_Array) return Sum_Of_Weights is
      Res : Float := 0.0;
   begin
      for I in Index loop
         Res := Res + Weights (I);
         pragma Loop_Invariant (Res = Sum_Weight_Rec (Weights, I));
      end loop;
      return Res;
   end Sum_Weight;

   function Weighted_Sum_Rec
     (Weights : Weight_Array;
      Values  : Value_Array;
      I       : Extended_Index) return Float
   is
      procedure Lemma_Add_Is_Monotonic
        (Min1, Val1, Max1, Min2, Val2, Max2 : Float)
      with
        Ghost,
        Pre  => Val1 in Min1 .. Max1
        and then Float'First / 2.0 <= Min1 and then Max1 <= Float'Last / 2.0
        and then Val2 in Min2 .. Max2
        and then Float'First / 2.0 <= Min2 and then Max2 <= Float'Last / 2.0,
        Post => Val1 + Val2 in Min1 + Min2 .. Max1 + Max2;
      --  The sum of 2 floating point values is in the sum of its bounds

      procedure Lemma_Add_Is_Monotonic
        (Min1, Val1, Max1, Min2, Val2, Max2 : Float)
      is null;

   begin
      if I = 0 then
         return 0.0;
      else
         Lemma_Add_Is_Monotonic
           (Min1 => -Max_Value,
            Val1 => Weights (I) * Values (I),
            Max1 => Max_Value,
            Min2 => -(Max_Value * Float (I - 1)),
            Val2 => Weighted_Sum_Rec (Weights, Values, I - 1),
            Max2 => Max_Value * Float (I - 1));
         Lemma_Integer_Mul_Exact (Max_Value, Float (I - 1), Max_Value_Int, I - 1);
         Lemma_Integer_Mul_Exact (Max_Value, Float (I), Max_Value_Int, I);
         Lemma_Integer_Add_Exact
           (Max_Value * Float (I - 1), Max_Value, Max_Value_Int * (I - 1), Max_Value_Int);
         return Weighted_Sum_Rec (Weights, Values, I - 1) + Weights (I) * Values (I);
      end if;
   end Weighted_Sum_Rec;

   function Weighted_Average
     (Weights : Weight_Array;
      Values  : Value_Array) return Sum_Of_Values
   is
      Num : Float := 0.0;
      Den : Float := 0.0;
   begin
      for I in Index loop
         Num := Num + Weights (I) * Values (I);
         Den := Den + Weights (I);
         pragma Loop_Invariant (Num = Weighted_Sum_Rec (Weights, Values, I));
         pragma Loop_Invariant (Den = Sum_Weight_Rec (Weights, I));
      end loop;
      return Num / Den;
   end Weighted_Average;

end Libst;
