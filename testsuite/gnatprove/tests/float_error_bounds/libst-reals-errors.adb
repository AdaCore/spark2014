with SPARK.Float_Arithmetic_Lemmas; use SPARK.Float_Arithmetic_Lemmas;

package body Libst.Reals.Errors with SPARK_Mode is

   --  Types for which the floating point operations are safe

   subtype Floats_For_Add is Float range Float'First / 2.0 .. Float'Last / 2.0;
   subtype Floats_For_Mul is Float range - Float_Sqrt .. Float_Sqrt;
   subtype Floats_For_Div is Float with
     Static_Predicate =>
       Floats_For_Div in Float'First .. - 1.0 / Float_Sqrt
                       | 1.0 / Float_Sqrt .. Float'Last;

   --  Proofs of error bound lemmas on our specification

   procedure Error_For_SW_Rec
     (Weights : Weight_Array;
      I       : Index)
   is

      --  Lemma: Aggregate together error bounds coming from:
      --    * The computation of the summation up to I - 1
      --    * The last addition

      procedure Aggregate_Bounds
        (Sum_F, W     : Floats_For_Add;
         Res_F        : Float;
         Sum_R, Res_R : Big_Real)
      with
        Pre => I > 1 and Sum_R >= 0.0 and Sum_F >= 0.0 and W >= 0.0
        and Res_F = Sum_F + W and Res_R = Sum_R + To_Big_Real (W)
        and abs (To_Big_Real (Sum_F) - Sum_R) <=
          5.972E-08 * To_Real (I - 2) * Sum_R
        and abs (To_Big_Real (Sum_F + W) - (To_Big_Real (Sum_F) + To_Big_Real (W)))
          <= 5.971E-08 * (To_Big_Real (Sum_F) + To_Big_Real (W)),
        Post => abs (To_Big_Real (Res_F) - Res_R)
          <= 5.972E-08 * To_Real (I - 1) * Res_R;
      procedure Aggregate_Bounds
        (Sum_F, W     : Floats_For_Add;
         Res_F        : Float;
         Sum_R, Res_R : Big_Real)
      is
      begin
         pragma Assert
           (5.97E-08 * To_Big_Real (W)
            <= 5.971E-08 * To_Real (I - 1) * To_Big_Real (W));
      end Aggregate_Bounds;

      Sum_F : constant Float := Sum_Weight_Rec (Weights, I - 1);
      Res_F : constant Float := Sum_Weight_Rec (Weights, I);
      W     : constant Float := Weights (I);
      Sum_R : constant Big_Real := Sum_Weight_Rec (Weights, I - 1);
      Res_R : constant Big_Real := Sum_Weight_Rec (Weights, I);

   begin
      if I = 1 then
         --  No error occurs when adding 0.0 to something
         pragma Assert
           (abs (To_Big_Real (Sum_Weight_Rec (Weights, I)) - Sum_Weight_Rec (Weights, I)) = 0.0);
      else
         --  Compute the error for the summation up to I - 1
         Error_For_SW_Rec (Weights, I - 1);
         --  Compute the error for the last addition
         Lemma_Rounding_Error_Add (Sum_Weight_Rec (Weights, I - 1), Weights (I));
         --  The weight is big enough that the absolute error term Eta can be
         --  ignored.
         pragma Assert (W = 0.0 or W >= Min_Weight);
         --  Aggregate together both bounds
         Aggregate_Bounds (Sum_F, W, Res_F, Sum_R, Res_R);
      end if;
   end Error_For_SW_Rec;

   procedure Error_For_SW (Weights : Weight_Array) is
   begin
      Error_For_SW_Rec (Weights, Max_Index);
   end Error_For_SW;

   procedure Sum_Less_Than_Sum_Abs
     (Weights : Weight_Array;
      Values  : Value_Array;
      I       : Extended_Index)
   is
   begin
      --  The proof is done by induction over the value of I
      if I /= 0 then
         --  Help the prover: Distributivity of abs over mutliplication
         pragma Assert (abs (To_Big_Real (Weights (I)) * To_Big_Real (Values (I)))
                        = To_Big_Real (Weights (I)) * abs (To_Big_Real (Values (I))));
         --  Recursive hypothesis for I - 1
         Sum_Less_Than_Sum_Abs (Weights, Values, I - 1);
      end if;
   end Sum_Less_Than_Sum_Abs;

   procedure Bound_Sum_Abs
     (Weights : Weight_Array;
      Values  : Value_Array;
      I       : Extended_Index)
   is
   begin
      --  The proof is done by induction over the value of I
      if I /= 0 then
         --  Recursive hypothesis for I - 1
         Bound_Sum_Abs (Weights, Values, I - 1);
         --  Help the prover: the absolute value of values are bounded by
         --  Max_Value
         pragma Assert
           (abs (To_Big_Real (Values (I))) <= To_Big_Real (Max_Value));
      end if;
   end Bound_Sum_Abs;

   procedure Error_For_Sum_Rec
     (Weights : Weight_Array;
      Values  : Value_Array;
      I       : Index)
   is

      --  Lemma: The summation up to I - 1 can be used inside additions

      procedure Bound_Weighted_Sum (Sum : Float) with
        Pre  => Sum in -(Max_Value * Float (I - 1)) .. Max_Value * Float (I - 1),
        Post => Sum in Floats_For_Add;
      procedure Bound_Weighted_Sum (Sum : Float) is null;

      --  Lemma: Lift the error bound on the top-level addition so that it is
      --     expressed in terms of the real functions.

      procedure EB_For_Add
        (Sum_F        : Floats_For_Add;
         W, V         : Floats_For_Mul;
         Sum_R, Sum_A : Big_Real)
      with
        Pre => I /= 1 and W >= 0.0 and abs (Sum_R) <= Sum_A
        and abs (To_Big_Real (Sum_F) - Sum_R)
          <= 1.403E-45 * To_Real (I - 1) + 5.971E-08 * To_Real (I - 1) * Sum_A
        and abs (To_Big_Real (Sum_F + W * V) - (To_Big_Real (Sum_F) + To_Big_Real (W * V)))
          <= 7.01E-46 + 5.97E-08 * abs (To_Big_Real (Sum_F) + To_Big_Real (W * V))
        and abs (To_Big_Real (W * V) - (To_Big_Real (W) * To_Big_Real (V)))
          <= 7.01E-46 + 5.97E-08 * abs (To_Big_Real (W) * To_Big_Real (V)),
        Post => abs (To_Big_Real (Sum_F + W * V) - (To_Big_Real (Sum_F) + To_Big_Real (W * V)))
          <= 7.011E-46 + 5.971E-08 * Sum_A + 5.971E-08 * To_Big_Real (W) * abs (To_Big_Real (V));
      procedure EB_For_Add
        (Sum_F        : Floats_For_Add;
         W, V         : Floats_For_Mul;
         Sum_R, Sum_A : Big_Real) is null;

      --  Lemma: Aggregate together error bounds coming from:
      --    * The computation of the summation up to I - 1
      --    * The last addition
      --    * The nested multiplication

      procedure Aggregate_Bounds
        (Sum_F        : Floats_For_Add;
         Res_F        : Floats_For_Add;
         W, V         : Floats_For_Mul;
         Sum_R, Sum_A : Big_Real;
         Res_R, Res_A : Big_Real)
      with
        Pre => I /= 1 and W >= 0.0 and abs (Sum_R) <= Sum_A
        and Res_F = Sum_F + W * V
        and Res_R = Sum_R + To_Big_Real (W) * To_Big_Real (V)
        and Res_A = Sum_A + To_Big_Real (W) * abs (To_Big_Real (V))
        and abs (To_Big_Real (Sum_F) - Sum_R)
          <= 1.403E-45 * To_Real (I - 1) + 5.971E-08 * To_Real (I - 1) * Sum_A
        and abs (To_Big_Real (Sum_F + W * V) - (To_Big_Real (Sum_F) + To_Big_Real (W * V)))
          <= 7.011E-46 + 5.971E-08 * Sum_A + 5.971E-08 * To_Big_Real (W) * abs (To_Big_Real (V))
        and abs (To_Big_Real (W * V) - (To_Big_Real (W) * To_Big_Real (V)))
          <= 7.01E-46 + 5.97E-08 * abs (To_Big_Real (W) * To_Big_Real (V)),
        Post => abs (To_Big_Real (Res_F) - Res_R)
          <= 1.403E-45 * To_Real (I) + 5.971E-08 * To_Real (I) * Res_A;
      procedure Aggregate_Bounds
        (Sum_F        : Floats_For_Add;
         Res_F        : Floats_For_Add;
         W, V         : Floats_For_Mul;
         Sum_R, Sum_A : Big_Real;
         Res_R, Res_A : Big_Real) is null;

      Sum_F : constant Float := Weighted_Sum_Rec (Weights, Values, I - 1);
      Res_F : constant Float := Weighted_Sum_Rec (Weights, Values, I);
      W     : constant Floats_For_Mul := Weights (I);
      V     : constant Floats_For_Mul := Values (I);
      Sum_R : constant Big_Real := Weighted_Sum_Rec (Weights, Values, I - 1);
      Sum_A : constant Big_Real := Weighted_Sum_Abs_Rec (Weights, Values, I - 1);
      Res_R : constant Big_Real := Weighted_Sum_Rec (Weights, Values, I);
      Res_A : constant Big_Real := Weighted_Sum_Abs_Rec (Weights, Values, I);

   begin
      if I = 1 then
         --  Compute the error for the multiplication
         Lemma_Rounding_Error_Mul (W, V);
         --  The prostcondition gives a correct error bound
         pragma Assert
           (abs (To_Big_Real (W * V) - To_Big_Real (W) * To_Big_Real (V))
            <= 1.403E-45 * To_Real (I)
            + 5.971E-08 * To_Real (I) * abs (To_Big_Real (W) * To_Big_Real (V)));
         pragma Assert
           (abs (To_Big_Real (Res_F) - Res_R)
            <= 1.403E-45 * To_Real (I) + 5.971E-08 * To_Real (I) * Res_A);
      else
         --  The summation up to I - 1 can be used inside additions
         Bound_Weighted_Sum (Sum_F);
         --  Compute the error for the summation up to I - 1
         Error_For_Sum_Rec (Weights, Values, I - 1);
         --  Compute the error for the last addition
         Lemma_Rounding_Error_Add (Sum_F, W * V);
         --  Compute the error for the multiplication
         Lemma_Rounding_Error_Mul (W, V);
         --  The absolute value of the weighted sum is less than the weighted
         --  sum of the absolute values.
         Sum_Less_Than_Sum_Abs (Weights, Values, I - 1);
         --  Lift the error bound on the top-level addition so that it is
         --  expressed in terms of the real functions.
         EB_For_Add (Sum_F, W, V, Sum_R, Sum_A);
         --  Aggregate together error bounds coming from all the computations
         Aggregate_Bounds (Sum_F, Res_F, W, V, Sum_R, Sum_A, Res_R, Res_A);
      end if;
   end Error_For_Sum_Rec;

   procedure Error_For_Sum
     (Weights : Weight_Array;
      Values  : Value_Array) is
   begin
      Error_For_Sum_Rec (Weights, Values, Max_Index);
   end Error_For_Sum;

   procedure Error_For_Average
     (Weights : Weight_Array;
      Values  : Value_Array)
   is

      --  Lemma: Lift the error bound on the computation of the numerator so
      --     that it is expressed in terms of the real functions.

      procedure EB_For_Sum
        (Num_F               : Floats_For_Mul;
         Den_F               : Floats_For_Div;
         Num_R, Den_R, Num_A : Big_Real)
      with
        Pre  => Den_F >= Min_Weight and Num_A >= abs (Num_R)
        and abs (To_Big_Real (Num_F) - Num_R) <= 1.403E-43 + 5.971E-06 * Num_A
        and abs (To_Big_Real (Den_F) - Den_R) <= 5.92E-06 * Den_R,
        Post => abs (To_Big_Real (Num_F) / To_Big_Real (Den_F) - Num_R / To_Big_Real (Den_F))
            <= 1.404E-43 / Den_R + 5.972E-06 * Num_A / Den_R;
      procedure EB_For_Sum
        (Num_F               : Floats_For_Mul;
         Den_F               : Floats_For_Div;
         Num_R, Den_R, Num_A : Big_Real)
      is
      begin
         pragma Assert (Den_R / To_Big_Real (Den_F) <= 1.0 + 5.921E-06);
      end EB_For_Sum;

      --  Lemma: Lift the error bound on the computation of the denominator so
      --     that it is expressed in terms of the real functions.

      procedure EB_For_Weights
        (Num_F               : Floats_For_Mul;
         Den_F               : Floats_For_Div;
         Num_R, Den_R, Num_A : Big_Real)
      with
        Pre  => Den_F >= Min_Weight and Den_F > 0.0 and Den_R > 0.0 and Num_A >= abs (Num_R)
        and abs (To_Big_Real (Num_F) - Num_R) <= 1.403E-43 + 5.971E-06 * Num_A
        and abs (To_Big_Real (Den_F) - Den_R) <= 5.92E-06 * Den_R,
        Post => abs (Num_R / To_Big_Real (Den_F) - Num_R / Den_R)
            <= 5.922E-06 * Num_A / Den_R;
      procedure EB_For_Weights
        (Num_F               : Floats_For_Mul;
         Den_F               : Floats_For_Div;
         Num_R, Den_R, Num_A : Big_Real)
      is null;


      --  Lemma: Lift the error bound on the division so that it is expressed
      --     in terms of the real functions.

      procedure EB_For_Div
        (Num_F               : Floats_For_Mul;
         Den_F               : Floats_For_Div;
         Num_R, Den_R, Num_A : Big_Real)
      with
        Pre  => Den_F > 0.0 and then Den_R > 0.0 and then Num_A >= abs (Num_R)
        and then abs (Num_R / To_Big_Real (Den_F) - Num_R / Den_R)
            <= 5.922E-06 * Num_A / Den_R
        and then abs (To_Big_Real (Num_F) / To_Big_Real (Den_F) - Num_R / To_Big_Real (Den_F))
            <= 1.404E-43 / Den_R + 5.972E-06 * Num_A / Den_R
        and then abs (To_Big_Real (Num_F / Den_F) - (To_Big_Real (Num_F) / To_Big_Real (Den_F)))
          <= 7.01E-46 + 5.97E-08 * abs (To_Big_Real (Num_F) / To_Big_Real (Den_F)),
        Post => abs (To_Big_Real (Num_F / Den_F) - (To_Big_Real (Num_F) / To_Big_Real (Den_F)))
            <= 7.011E-46 + 5.971E-08 * Num_A / Den_R + 1.404E-43 / Den_R;
      procedure EB_For_Div
        (Num_F               : Floats_For_Mul;
         Den_F               : Floats_For_Div;
         Num_R, Den_R, Num_A : Big_Real) is
      begin
         pragma Assert (abs (To_Big_Real (Num_F) / To_Big_Real (Den_F)) <=
                          abs (To_Big_Real (Num_F) / To_Big_Real (Den_F) - Num_R / To_Big_Real (Den_F))
                        + abs (Num_R / To_Big_Real (Den_F) - Num_R / Den_R)
                        + Num_A / Den_R);
         pragma Assert (5.97E-08 * abs (To_Big_Real (Num_F) / To_Big_Real (Den_F)) <=
                          5.97E-08 * (Num_A / Den_R + 1.404E-43 / Den_R + 1.19E-05 * Num_A / Den_R));
         pragma Assert (5.97E-08 * Num_A / Den_R + 5.97E-08 * 1.19E-05 * Num_A / Den_R <= 5.971E-08 * Num_A / Den_R);
      end EB_For_Div;

      --  Lemma: Aggregate together error bounds coming from:
      --    * The computation of numerator
      --    * The computation of denominator
      --    * The division

      procedure Aggregate_Bounds
        (Num_F               : Floats_For_Mul;
         Den_F               : Floats_For_Div;
         Res_F               : Float;
         Num_R, Den_R, Num_A : Big_Real;
         Res_R, Res_A        : Big_Real)
      with
        Pre  => Den_R > 0.0 and then Num_A >= 0.0
        and then Res_F = Num_F / Den_F
        and then Res_R = Num_R / Den_R and then Res_A = Num_A / Den_R
        and then abs (To_Big_Real (Num_F / Den_F) - (To_Big_Real (Num_F) / To_Big_Real (Den_F)))
          <= 7.011E-46 + 5.971E-08 * Num_A / Den_R + 1.404E-43 / Den_R
        and then abs (To_Big_Real (Num_F) / To_Big_Real (Den_F) - Num_R / To_Big_Real (Den_F))
          <= 1.404E-43 / Den_R + 5.972E-06 * Num_A / Den_R
        and then abs (Num_R / To_Big_Real (Den_F) - Num_R / Den_R) <= 5.922E-06 * Num_A / Den_R,
        Post => abs (To_Big_Real (Res_F)- Res_R) <= 7.011E-46 + 2.808E-43 / Den_R + 1.2E-5 * Res_A;
      procedure Aggregate_Bounds
        (Num_F               : Floats_For_Mul;
         Den_F               : Floats_For_Div;
         Res_F               : Float;
         Num_R, Den_R, Num_A : Big_Real;
         Res_R, Res_A        : Big_Real)
      is
      begin
         pragma Assert
           (7.011E-46 + 5.971E-08 * Num_A / Den_R + 1.404E-43 / Den_R
            + 1.404E-43 / Den_R + 5.972E-06 * Num_A / Den_R
            + 5.922E-06 * Num_A / Den_R
            <= 7.011E-46 + 2.808E-43 / Den_R + 1.2E-5 * Num_A / Den_R);
         pragma Assert
           (abs (To_Big_Real (Num_F / Den_F) - (To_Big_Real (Num_F) / To_Big_Real (Den_F)))
            + abs (To_Big_Real (Num_F) / To_Big_Real (Den_F) - Num_R / To_Big_Real (Den_F))
            + abs (Num_R / To_Big_Real (Den_F) - Num_R / Den_R)
            <= 7.011E-46 + 2.808E-43 / Den_R + 1.2E-5 * Num_A / Den_R);
      end Aggregate_Bounds;

      Num_F : constant Float := Weighted_Sum_Rec (Weights, Values, Max_Index);
      Den_F : constant Float := Sum_Weight (Weights);
      Res_F : Float; --  Will be set to Weighted_Average (Weights, Values) once its precondition can be proved
      Num_R : constant Big_Real := Weighted_Sum_Rec (Weights, Values, Max_Index);
      Den_R : constant Big_Real := Sum_Weight (Weights);
      Num_A : constant Big_Real := Weighted_Sum_Abs_Rec (Weights, Values, Max_Index);
      Res_R : constant Big_Real := Weighted_Average (Weights, Values);
      Res_A : constant Big_Real := Weighted_Average_Abs (Weights, Values);

   begin
      --  Compute the error for the numerator
      Error_For_Sum (Weights, Values);
      --  Compute the error for the denominator
      Error_For_SW (Weights);
      pragma Assert (Den_F >= Min_Weight);
      Res_F := Weighted_Average (Weights, Values);
      --  Compute the error for the division
      Lemma_Rounding_Error_Div (Num_F, Den_F);
      --  The absolute value of the weighted sum is less than the weighted
      --  sum of the absolute values.
      Sum_Less_Than_Sum_Abs (Weights, Values, Max_Index);
      --  Lift all error bounds so that they refer to real functions
      EB_For_Sum (Num_F, Den_F, Num_R, Den_R, Num_A);
      EB_For_Weights (Num_F, Den_F, Num_R, Den_R, Num_A);
      EB_For_Div (Num_F, Den_F, Num_R, Den_R, Num_A);
      --  Aggregate together error bounds coming from all the computations
      Aggregate_Bounds (Num_F, Den_F, Res_F, Num_R, Den_R, Num_A, Res_R, Res_A);
   end Error_For_Average;

   procedure Precise_Bounds_For_Average
     (Weights : Weight_Array;
      Values  : Value_Array)
   is
      --  Lemma: Prove by induction that Sum_Weight is either 0.0 or more than
      --         Min_Weight on real numbers

      procedure Min_For_SW (I : Extended_Index) with
        Subprogram_Variant => (Decreases => I),
        Post => Sum_Weight_Rec (Weights, I) = Big_Real'(0.0)
        or else Sum_Weight_Rec (Weights, I) >= To_Big_Real (Min_Weight)
      is
      begin
         if I /= 0 then
            Min_For_SW (I - 1);
         end if;
      end Min_For_SW;

   begin
      --  Sum_Weight (Weights) in floats is not 0.0
      Error_For_SW (Weights);
      --  Compute the error for the computation of Weighted_Average
      Error_For_Average (Weights, Values);
      --  Bound Weighted_Sum_Rec and Weighted_Sum_Abs by Max_Value on real numbers
      Sum_Less_Than_Sum_Abs (Weights, Values, Max_Index);
      Bound_Sum_Abs (Weights, Values, Max_Index);
      pragma Assert (Weighted_Average_Abs (Weights, Values) <= To_Big_Real (Max_Value));
      --  Sum_Weight is more than Min_Weight on real numbers
      Min_For_SW (Max_Index);
      pragma Assert (Sum_Weight (Weights) >= To_Big_Real (Min_Weight));

      --  Compute the most precise bound for Weighted_Average on floats given by
      --  the error bound on the computation and the bound on real numbers.
      pragma Assert
        (abs (To_Big_Real (Float'(Weighted_Average (Weights, Values)))) <=
           To_Big_Real (Max_Value) + 1.25E-45 + 2.52E-43 / To_Big_Real (Min_Weight)
         + 2.05E-5 * To_Big_Real (Max_Value));
   end Precise_Bounds_For_Average;

end Libst.Reals.Errors;
