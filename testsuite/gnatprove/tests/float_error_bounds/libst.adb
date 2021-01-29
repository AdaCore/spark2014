with SPARK.Float_Arithmetic_Lemmas; use SPARK.Float_Arithmetic_Lemmas;

package body Libst with SPARK_Mode is

   function Sum_Weight_Rec
     (Weights : Weight_Array;
      I       : Extended_Index) return Float
   is

      procedure Lemma_Add_Exact_On_Index (I, J : Natural) with
        Ghost,
        Pre  => I <= Max_Index and J <= Max_Index,
        Post => Float (I) + Float (J) = Float (I + J);
      --  Floating-point addition is exact on values of Index

      procedure Lemma_Add_Exact_On_Index (I, J : Natural) is null;

   begin
      if I = 0 then
         return 0.0;
      else
         Lemma_Add_Exact_On_Index (I - 1, 1);
         return Sum_Weight_Rec (Weights, I - 1) + Weights (I);
      end if;
   end Sum_Weight_Rec;

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
      is
      begin
         Lemma_Add_Is_Monotonic (Val1, Max1, Val2);
         Lemma_Add_Is_Monotonic (Val2, Max2, Max1);
         Lemma_Add_Is_Monotonic (Min1, Val1, Val2);
         Lemma_Add_Is_Monotonic (Min2, Val2, Min1);
      end Lemma_Add_Is_Monotonic;

      procedure Lemma_Add_Exact_On_Max_Value (I : Natural) with
        Ghost,
        Pre  => I < Max_Index,
        Post => Max_Value * Float (I) + Max_Value = Max_Value * Float (I + 1)
        and -(Max_Value * Float (I)) - Max_Value = -(Max_Value * Float (I + 1));
      --  Compuations on Max_Value are exact

      procedure Lemma_Add_Exact_On_Max_Value (I : Natural) is
         Max_Value_Int : constant Integer := Integer (Max_Value);
      begin
         pragma Assert
           (Max_Value * Float (I) = Float (Max_Value_Int * I));
         pragma Assert (Max_Value * Float (I) + Max_Value =
                          Float (Max_Value_Int * I + Max_Value_Int));
         pragma Assert
           (Max_Value * Float (I + 1) = Float (Max_Value_Int * (I + 1)));
      end Lemma_Add_Exact_On_Max_Value;

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
         Lemma_Add_Exact_On_Max_Value (I - 1);
         return Weighted_Sum_Rec (Weights, Values, I - 1) + Weights (I) * Values (I);
      end if;
   end Weighted_Sum_Rec;

end Libst;
