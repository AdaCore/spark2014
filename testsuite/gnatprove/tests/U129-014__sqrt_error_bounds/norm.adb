with SPARK.Lemmas.Float_Arithmetic; use SPARK.Lemmas.Float_Arithmetic;
with Sqrt_Spec;

package body Norm with SPARK_Mode is

   function Sum_Of_Squares_Rec
     (Values : Value_Array;
      I      : Extended_Index) return Float
   is
      procedure Lemma_Add_Square_Is_Monotonic
        (Val1, Max1, Val2, Max2 : Float)
      with
        Ghost,
        Pre  => Val1 in -Max1 .. Max1
        and then Max1 <= Float_Sqrt
        and then Max1 ** 2 <= Float'Last / 2.0
        and then Val2 in 0.0 .. Max2
        and then Max2 <= Float'Last / 2.0,
        Post => Val1 ** 2 + Val2 in 0.0 .. Max1 ** 2 + Max2;
      --  Bound the sum of the square of a floating point values

      procedure Lemma_Add_Square_Is_Monotonic
        (Val1, Max1, Val2, Max2 : Float)
      is
      begin
         Lemma_Mult_Is_Monotonic (abs (Val1), Max1, abs (Val1));
         Lemma_Mult_Is_Monotonic (abs (Val1), Max1, Max1);
         Lemma_Add_Is_Monotonic (Val1 ** 2, Max1 ** 2, Val2);
         Lemma_Add_Is_Monotonic (Val2, Max2, Max1 ** 2);
      end Lemma_Add_Square_Is_Monotonic;

      procedure Lemma_Add_Exact_On_Max_Value (I : Natural) with
        Ghost,
        Pre  => I < Max_Index,
        Post => Max_Value * Max_Value * Float (I) + Max_Value * Max_Value =
          Max_Value * Max_Value * Float (I + 1);
      --  Compuations on Max_Value are exact

      procedure Lemma_Add_Exact_On_Max_Value (I : Natural) is
         Max_Value_Int : constant Integer := Integer (Max_Value);
      begin
         pragma Assert
           (Max_Value ** 2 * Float (I) =
                Float (Max_Value_Int * Max_Value_Int * I));
         pragma Assert
           (Max_Value ** 2 * Float (I) + Max_Value * Max_Value =
                Float (Max_Value_Int ** 2 * I +
                  Max_Value_Int ** 2));
         pragma Assert
           (Max_Value ** 2 * Float (I + 1) =
                Float (Max_Value_Int ** 2 * (I + 1)));
      end Lemma_Add_Exact_On_Max_Value;

   begin
      if I = 0 then
         return 0.0;
      else
         Lemma_Add_Square_Is_Monotonic
           (Val1 => Values (I),
            Max1 => Max_Value,
            Val2 => Sum_Of_Squares_Rec (Values, I - 1),
            Max2 => Max_Value ** 2 * Float (I - 1));
         Lemma_Add_Exact_On_Max_Value (I - 1);
         return Sum_Of_Squares_Rec (Values, I - 1) + Values (I) ** 2;
      end if;
   end Sum_Of_Squares_Rec;

   function Norm (Values : Value_Array) return Norm_Type is
      Result : constant Float := Sqrt (Sum_Of_Squares_Rec (Values, Max_Index));
   begin
      Sqrt_Spec.Sqrt_Is_Monotonic
        (Sum_Of_Squares_Rec (Values, Max_Index),
         Max_Value ** 2 * Float (Max_Index));
      Sqrt_Spec.Sqrt_Exact_Integer (2890);
      return Result;
   end Norm;

end Norm;
