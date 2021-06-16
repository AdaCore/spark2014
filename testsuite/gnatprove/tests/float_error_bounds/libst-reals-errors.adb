package body Libst.Reals.Errors with SPARK_Mode is

   Epsilon      : constant := 1.0E-7;
   pragma Assert (2.0 ** (-24) <= Epsilon);
   --  Over-approximation of the machine epsilon for 32bits floats
   First_Norm   : constant := 1.2E-38;
   pragma Assert (2.0 ** (-126) <= First_Norm);
   --  Over-approximation of the first positive normal number
   Error_Denorm : constant := 1.0E-45;
   pragma Assert (2.0 ** (-150) <= Error_Denorm);
   --  Over-approximation of the error bound on denormal numbers

   --  Types for which the floating point operations are safe

   subtype Floats_For_Add is Float range Float'First / 2.0 .. Float'Last / 2.0;
   subtype Floats_For_Mul is Float range - Float_Sqrt .. Float_Sqrt;
   subtype Floats_For_Div is Float with
     Static_Predicate =>
       Floats_For_Div in Float'First .. - 1.0 / Float_Sqrt
                       | 1.0 / Float_Sqrt .. Float'Last;

   --  Lemmas giving an error bound for each binary operator

   procedure Bound_Error_Sub (X, Y : Floats_For_Add) with
     Post => abs (To_Big_Real (X - Y) - (To_Big_Real (X) - To_Big_Real (Y))) <=
       (if abs (To_Big_Real (X) - To_Big_Real (Y)) >= Big_Real'(First_Norm)
        then Big_Real'(Epsilon) * abs (To_Big_Real (X) - To_Big_Real (Y))
        else Error_Denorm);
   procedure Bound_Error_Sub (X, Y : Floats_For_Add) is null;
   procedure Bound_Error_Add (X, Y : Floats_For_Add) with
     Post => abs (To_Big_Real (X + Y) - (To_Big_Real (X) + To_Big_Real (Y))) <=
       (if abs (To_Big_Real (X) + To_Big_Real (Y)) >= Big_Real'(First_Norm)
        then Big_Real'(Epsilon) * abs (To_Big_Real (X) + To_Big_Real (Y))
        else Error_Denorm);
   procedure Bound_Error_Add (X, Y : Floats_For_Add) is null;
   procedure Bound_Error_Mul (X, Y : Floats_For_Mul) with
     Post => abs (To_Big_Real (X * Y) - To_Big_Real (X) * To_Big_Real (Y)) <=
       (if abs (To_Big_Real (X) * To_Big_Real (Y)) >= Big_Real'(First_Norm)
        then Big_Real'(Epsilon) * abs (To_Big_Real (X) * To_Big_Real (Y))
        else Error_Denorm);
   procedure Bound_Error_Mul (X, Y : Floats_For_Mul) is null;
   procedure Bound_Error_Div (X : Floats_For_Mul; Y : Floats_For_Div) with
     Post => abs (To_Big_Real (X / Y) - To_Big_Real (X) / To_Big_Real (Y)) <=
       (if abs (To_Big_Real (X) / To_Big_Real (Y)) >= Big_Real'(First_Norm)
        then Big_Real'(Epsilon) * abs (To_Big_Real (X) / To_Big_Real (Y))
        else Error_Denorm);
   procedure Bound_Error_Div (X : Floats_For_Mul; Y : Floats_For_Div) is null;

   --  Proofs of error bound lemmas on our specification

   procedure Error_For_SW_Rec
     (Weights : Weight_Array;
      I       : Index)
   is

      --  Lemma: Aggregate together error bounds coming from:
      --    * The computation of the summation up to I - 1
      --    * The last addition

      procedure Aggregate_Bounds
        (Sum_F, W : Floats_For_Add;
         Sum_R    : Valid_Big_Real)
      with
        Pre => I > 1 and Sum_R >= 0.0 and Sum_F >= 0.0 and W >= 0.0
        and abs (To_Big_Real (Sum_F) - Sum_R) <= 1.01E-7 * To_Real (I - 2) * Sum_R
        and abs (To_Big_Real (Sum_F + W) - (To_Big_Real (Sum_F) + To_Big_Real (W)))
          <= 1.0E-7 * (To_Big_Real (Sum_F) + To_Big_Real (W)),
        Post => abs (To_Big_Real (Sum_F + W) - (Sum_R + To_Big_Real (W)))
          <= 1.01E-7 * To_Real (I - 1) * (Sum_R + To_Big_Real (W));
      procedure Aggregate_Bounds
        (Sum_F, W : Floats_For_Add;
         Sum_R    : Valid_Big_Real) is null;

   begin
      if I = 1 then
         --  No error occurs when adding 0.0 to something
         pragma Assert
           (abs (To_Big_Real (Sum_Weight_Rec (Weights, I)) - Sum_Weight_Rec (Weights, I)) = 0.0);
      else
         --  Compute the error for the summation up to I - 1
         Error_For_SW_Rec (Weights, I - 1);
         --  Compute the error for the last addition
         Bound_Error_Add (Sum_Weight_Rec (Weights, I - 1), Weights (I));
         --  We don't need to consider denormal numbers here
         pragma Assert (Weights (I) = 0.0 or To_Big_Real (Weights (I)) >= Big_Real'(First_Norm));
         --  Aggregate together both bounds
         Aggregate_Bounds
           (Sum_Weight_Rec (Weights, I - 1), Weights (I), Sum_Weight_Rec (Weights, I - 1));
         --  Help the prover: Unfold the definition of Sum_Weight_Rec
         pragma Assert
           (abs (To_Big_Real (Sum_Weight_Rec (Weights, I)) - Sum_Weight_Rec (Weights, I))
            <= 1.01E-7 * To_Real (I - 1) * (Sum_Weight_Rec (Weights, I - 1) + To_Big_Real (Weights (I))));
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

      procedure Lift_Bounds
        (Sum_F        : Floats_For_Add;
         W, V         : Floats_For_Mul;
         Sum_R, Sum_A : Valid_Big_Real)
      with
        Pre => I /= 1 and W >= 0.0 and abs (Sum_R) <= Sum_A
        and abs (To_Big_Real (Sum_F) - Sum_R)
          <= 2.5E-45 * To_Real (I - 1) + (1.0E-7 + 1.01E-7 * To_Real (I - 2)) * Sum_A
        and abs (To_Big_Real (Sum_F + W * V) - (To_Big_Real (Sum_F) + To_Big_Real (W * V)))
          <= 1.2E-45 + 1.0E-7 * abs (To_Big_Real (Sum_F) + To_Big_Real (W * V))
        and abs (To_Big_Real (W * V) - (To_Big_Real (W) * To_Big_Real (V)))
          <= 1.2E-45 + 1.0E-7 * abs (To_Big_Real (W) * To_Big_Real (V)),
        Post => abs (To_Big_Real (Sum_F + W * V) - (To_Big_Real (Sum_F) + To_Big_Real (W * V)))
          <= 1.21E-45 + 1.01E-7 * Sum_A + 1.01E-7 * To_Big_Real (W) * abs (To_Big_Real (V));
      procedure Lift_Bounds
        (Sum_F        : Floats_For_Add;
         W, V         : Floats_For_Mul;
         Sum_R, Sum_A : Valid_Big_Real) is
      begin
         pragma Assert
           (1.0E-7 * abs (To_Big_Real (Sum_F)) <= 1.0E-47 + 1.01E-7 * Sum_A);
      end Lift_Bounds;

      --  Lemma: Aggregate together error bounds coming from:
      --    * The computation of the summation up to I - 1
      --    * The last addition
      --    * The nested multiplication

      procedure Aggregate_Bounds
        (Sum_F        : Floats_For_Add;
         W, V         : Floats_For_Mul;
         Sum_R, Sum_A : Valid_Big_Real)
      with
        Pre => I /= 1 and W >= 0.0 and abs (Sum_R) <= Sum_A
        and abs (To_Big_Real (Sum_F) - Sum_R)
          <= 2.5E-45 * To_Real (I - 1) + (1.0E-7 + 1.01E-7 * To_Real (I - 2)) * Sum_A
        and abs (To_Big_Real (Sum_F + W * V) - (To_Big_Real (Sum_F) + To_Big_Real (W * V)))
          <= 1.21E-45 + 1.01E-7 * Sum_A + 1.01E-7 * To_Big_Real (W) * abs (To_Big_Real (V))
        and abs (To_Big_Real (W * V) - (To_Big_Real (W) * To_Big_Real (V)))
          <= 1.2E-45 + 1.0E-7 * abs (To_Big_Real (W) * To_Big_Real (V)),
        Post => abs (To_Big_Real (Sum_F + W * V) - (Sum_R + To_Big_Real (W) * To_Big_Real (V)))
          <= 2.5E-45 * To_Real (I) + (1.0E-7 + 1.01E-7 * To_Real (I - 1))
           * (Sum_A + To_Big_Real (W) * abs (To_Big_Real (V)));
      procedure Aggregate_Bounds
        (Sum_F        : Floats_For_Add;
         W, V         : Floats_For_Mul;
         Sum_R, Sum_A : Valid_Big_Real) is null;

      --  Lemma: The prostcondition gives a correct error bound when I is 1

      procedure Prove_Post_First
        (Sum_F        : Floats_For_Add;
         Pre_F        : Floats_For_Add;
         W, V         : Floats_For_Mul;
         Sum_R, Sum_A : Valid_Big_Real;
         Pre_R, Pre_A : Valid_Big_Real)
      with
        Pre  => W >= 0.0
        and Sum_F = W * V + Pre_F and Sum_R = To_Big_Real (W) * To_Big_Real (V) + Pre_R
        and Sum_A = To_Big_Real (W) * abs (To_Big_Real (V)) + Pre_A
        and Pre_F = 0.0 and Pre_A = 0.0 and Pre_R = 0.0
        and abs (To_Big_Real (W * V) - To_Big_Real (W) * To_Big_Real (V))
          <= 1.2E-45 + 1.0E-7 * To_Big_Real (W) * abs (To_Big_Real (V)),
        Post => abs (To_Big_Real (Sum_F) - Sum_R)
          <= 2.5E-45 * To_Real (I) + (1.0E-7 + 1.01E-7 * To_Real (I - 1)) * Sum_A;
      procedure Prove_Post_First
        (Sum_F        : Floats_For_Add;
         Pre_F        : Floats_For_Add;
         W, V         : Floats_For_Mul;
         Sum_R, Sum_A : Valid_Big_Real;
         Pre_R, Pre_A : Valid_Big_Real) is null;

      --  Lemma: The prostcondition gives a correct error bound when I is more
      --     than 1.

      procedure Prove_Post
        (Sum_F        : Floats_For_Add;
         Pre_F        : Floats_For_Add;
         W, V         : Floats_For_Mul;
         Sum_R, Sum_A : Valid_Big_Real;
         Pre_R, Pre_A : Valid_Big_Real)
      with
        Pre  => Sum_F = W * V + Pre_F and Sum_R = To_Big_Real (W) * To_Big_Real (V) + Pre_R
        and Sum_A = To_Big_Real (W) * abs (To_Big_Real (V)) + Pre_A
        and abs (To_Big_Real (W * V + Pre_F) - (To_Big_Real (W) * To_Big_Real (V) + Pre_R))
          <= 2.5E-45 * To_Real (I) + (1.0E-7 + 1.01E-7 * To_Real (I - 1))
           * (To_Big_Real (W) * abs (To_Big_Real (V)) + Pre_A),
        Post => abs (To_Big_Real (Sum_F) - Sum_R)
          <= 2.5E-45 * To_Real (I) + (1.0E-7 + 1.01E-7 * To_Real (I - 1)) * Sum_A;
      procedure Prove_Post
        (Sum_F        : Floats_For_Add;
         Pre_F        : Floats_For_Add;
         W, V         : Floats_For_Mul;
         Sum_R, Sum_A : Valid_Big_Real;
         Pre_R, Pre_A : Valid_Big_Real) is null;

   begin
      if I = 1 then
         --  Compute the error for the multiplication
        Bound_Error_Mul (Weights (I), Values (I));
         --  The prostcondition gives a correct error bound
        Prove_Post_First
           (Sum_F => Weighted_Sum_Rec (Weights, Values, I),
            Pre_F => Weighted_Sum_Rec (Weights, Values, I - 1),
            W     => Weights (I),
            V     => Values (I),
            Sum_R => Weighted_Sum_Rec (Weights, Values, I),
            Sum_A => Weighted_Sum_Abs_Rec (Weights, Values, I),
            Pre_R => Weighted_Sum_Rec (Weights, Values, I - 1),
            Pre_A => Weighted_Sum_Abs_Rec (Weights, Values, I - 1));
      else
         --  The summation up to I - 1 can be used inside additions
         Bound_Weighted_Sum (Weighted_Sum_Rec (Weights, Values, I - 1));
         --  Compute the error for the summation up to I - 1
         Error_For_Sum_Rec (Weights, Values, I - 1);
         --  Compute the error for the last addition
         Bound_Error_Add
           (Weighted_Sum_Rec (Weights, Values, I - 1), Weights (I) * Values (I));
         --  Compute the error for the multiplication
         Bound_Error_Mul (Weights (I), Values (I));
         --  The absolute value of the weighted sum is less than the weighted
         --  sum of the absolute values.
         Sum_Less_Than_Sum_Abs (Weights, Values, I - 1);
         --  Lift the error bound on the top-level addition so that it is
         --  expressed in terms of the real functions.
         Lift_Bounds
           (Sum_F => Weighted_Sum_Rec (Weights, Values, I - 1),
            W     => Weights (I),
            V     => Values (I),
            Sum_R => Weighted_Sum_Rec (Weights, Values, I - 1),
            Sum_A => Weighted_Sum_Abs_Rec (Weights, Values, I - 1));
         --  Aggregate together error bounds coming from all the computations
         Aggregate_Bounds
           (Sum_F => Weighted_Sum_Rec (Weights, Values, I - 1),
            W     => Weights (I),
            V     => Values (I),
            Sum_R => Weighted_Sum_Rec (Weights, Values, I - 1),
            Sum_A => Weighted_Sum_Abs_Rec (Weights, Values, I - 1));
         --  The prostcondition gives a correct error bound
         Prove_Post
           (Sum_F => Weighted_Sum_Rec (Weights, Values, I),
            Pre_F => Weighted_Sum_Rec (Weights, Values, I - 1),
            W     => Weights (I),
            V     => Values (I),
            Sum_R => Weighted_Sum_Rec (Weights, Values, I),
            Sum_A => Weighted_Sum_Abs_Rec (Weights, Values, I),
            Pre_R => Weighted_Sum_Rec (Weights, Values, I - 1),
            Pre_A => Weighted_Sum_Abs_Rec (Weights, Values, I - 1));
      end if;
   end Error_For_Sum_Rec;

   procedure Error_For_Sum
     (Weights : Weight_Array;
      Values  : Value_Array)
   is

      --  Lemma: Lift the error bound on the computation of the numerator so
      --     that it is expressed in terms of the real functions.

      procedure Lift_Bounds_1
        (Num_F               : Floats_For_Mul;
         Den_F               : Floats_For_Div;
         Num_R, Den_R, Num_A : Valid_Big_Real)
      with
        Pre  => Den_F > 0.0 and Den_R > 0.0 and Num_A >= abs (Num_R)
        and abs (To_Big_Real (Num_F) - Num_R) <= 2.5E-43 + 1.01E-5 * Num_A
        and abs (To_Big_Real (Den_F) - Den_R) <= 1.0E-5 * Den_R,
        Post => abs (To_Big_Real (Num_F) / To_Big_Real (Den_F) - Num_R / To_Big_Real (Den_F))
            <= 2.51E-43 / Den_R + 1.02E-5 * Num_A / Den_R;
      procedure Lift_Bounds_1
        (Num_F               : Floats_For_Mul;
         Den_F               : Floats_For_Div;
         Num_R, Den_R, Num_A : Valid_Big_Real) is null;

      --  Lemma: Lift the error bound on the computation of the denominator so
      --     that it is expressed in terms of the real functions.

      procedure Lift_Bounds_2
        (Num_F               : Floats_For_Mul;
         Den_F               : Floats_For_Div;
         Num_R, Den_R, Num_A : Valid_Big_Real)
      with
        Pre  => Den_F > 0.0 and Den_R > 0.0 and Num_A >= abs (Num_R)
        and abs (To_Big_Real (Num_F) - Num_R) <= 2.5E-43 + 1.01E-5 * Num_A
        and abs (To_Big_Real (Den_F) - Den_R) <= 1.0E-5 * Den_R,
        Post => abs (Num_R / To_Big_Real (Den_F) - Num_R / Den_R)
            <= 1.01E-5 * Num_A / Den_R;
      procedure Lift_Bounds_2
        (Num_F               : Floats_For_Mul;
         Den_F               : Floats_For_Div;
         Num_R, Den_R, Num_A : Valid_Big_Real) is null;

      --  Lemma: Lift the error bound on the division so that it is expressed
      --     in terms of the real functions.

      procedure Lift_Bounds_3
        (Num_F               : Floats_For_Mul;
         Den_F               : Floats_For_Div;
         Num_R, Den_R, Num_A : Valid_Big_Real)
      with
        Pre  => Den_F > 0.0 and then Den_R > 0.0 and then Num_A >= abs (Num_R)
        and then abs (To_Big_Real (Num_F) / To_Big_Real (Den_F) - Num_R / Den_R)
            <= 2.51E-43 / Den_R + 2.03E-5 * Num_A / Den_R
        and then abs (To_Big_Real (Num_F / Den_F)- (To_Big_Real (Num_F) / To_Big_Real (Den_F)))
          <= 1.2E-45 + 1.0E-7 * abs (To_Big_Real (Num_F) / To_Big_Real (Den_F)),
        Post => abs (To_Big_Real (Num_F / Den_F) - (To_Big_Real (Num_F) / To_Big_Real (Den_F)))
            <= 1.25E-45 + 1.01E-7 * Num_A / Den_R + 2.51E-50 / Den_R;
      procedure Lift_Bounds_3
        (Num_F               : Floats_For_Mul;
         Den_F               : Floats_For_Div;
         Num_R, Den_R, Num_A : Valid_Big_Real) is
      begin
         pragma Assert (1.0E-7 * abs (To_Big_Real (Num_F) / To_Big_Real (Den_F)) <=
                          1.0E-7 * (Num_A / Den_R + 2.51E-43 / Den_R + 2.03E-5 * Num_A / Den_R));
      end Lift_Bounds_3;

      --  Lemma: Merge the three errors into a single one

      procedure Merge_Diffs
        (Diff1, Diff2, Diff3 : Valid_Big_Real;
         Den_R, Num_A        : Valid_Big_Real)
      with
        Pre  => Den_R > 0.0 and then Num_A >= 0.0
        and then Diff1 <= 1.25E-45 + 1.01E-7 * Num_A / Den_R + 2.51E-50 / Den_R
        and then Diff2 <= 2.51E-43 / Den_R + 1.02E-5 * Num_A / Den_R
        and then Diff3 <= 1.01E-5 * Num_A / Den_R,
        Post => Diff1 + Diff2 + Diff3 <= 1.25E-45 + 2.52E-43 / Den_R + 2.05E-5 * Num_A / Den_R;
      procedure Merge_Diffs
        (Diff1, Diff2, Diff3 : Valid_Big_Real;
         Den_R, Num_A        : Valid_Big_Real) is null;

      --  Lemma: Aggregate together error bounds coming from:
      --    * The computation of numerator
      --    * The computation of denominator
      --    * The division

      procedure Aggregate_Bounds
        (Num_F               : Floats_For_Mul;
         Den_F               : Floats_For_Div;
         Num_R, Den_R, Num_A : Valid_Big_Real)
      with
        Pre  => Den_F > 0.0 and Den_R > 0.0 and Num_A >= abs (Num_R)
        and abs (To_Big_Real (Num_F) - Num_R) <=
          2.5E-45 * To_Real (Max_Index) + (1.0E-7 + 1.01E-7 * To_Real (Max_Index - 1))  * Num_A
        and abs (To_Big_Real (Den_F) - Den_R) <= 1.0E-5 * Den_R
        and abs (To_Big_Real (Num_F / Den_F)- (To_Big_Real (Num_F) / To_Big_Real (Den_F)))
          <= 1.2E-45 + 1.0E-7 * abs (To_Big_Real (Num_F) / To_Big_Real (Den_F)),
        Post => abs (To_Big_Real (Num_F / Den_F)- Num_R / Den_R)
          <= 1.25E-45 + 2.52E-43 / Den_R + 2.05E-5 * Num_A / Den_R;
      procedure Aggregate_Bounds
        (Num_F               : Floats_For_Mul;
         Den_F               : Floats_For_Div;
         Num_R, Den_R, Num_A : Valid_Big_Real)
      is
      begin
         --  Left all error bounds so that they refer to real functions

         Lift_Bounds_1 (Num_F, Den_F, Num_R, Den_R, Num_A);
         Lift_Bounds_2 (Num_F, Den_F, Num_R, Den_R, Num_A);
         Lift_Bounds_3 (Num_F, Den_F, Num_R, Den_R, Num_A);

         --  Merge the them into a single one

         Merge_Diffs
           (Diff1 => abs (To_Big_Real (Num_F / Den_F) - (To_Big_Real (Num_F) / To_Big_Real (Den_F))),
            Diff2 => abs (To_Big_Real (Num_F) / To_Big_Real (Den_F) - Num_R / To_Big_Real (Den_F)),
            Diff3 => abs (Num_R / To_Big_Real (Den_F) - Num_R / Den_R),
            Den_R => Den_R,
            Num_A => Num_A);
      end Aggregate_Bounds;

   begin
      --  Compute the error for the denominator
      Error_For_SW (Weights);
      pragma Assert (Sum_Weight (Weights) >= Min_Weight);
      --  Compute the error for the numerator
      Error_For_Sum_Rec (Weights, Values, Max_Index);
      --  Compute the error for the division
      Bound_Error_Div
        (Weighted_Sum_Rec (Weights, Values, Max_Index), Sum_Weight (Weights));
      --  The absolute value of the weighted sum is less than the weighted
      --  sum of the absolute values.
      Sum_Less_Than_Sum_Abs (Weights, Values, Max_Index);
      --  Aggregate together error bounds coming from all the computations
      Aggregate_Bounds
        (Num_F => Weighted_Sum_Rec (Weights, Values, Max_Index),
         Den_F => Sum_Weight (Weights),
         Num_R => Weighted_Sum_Rec (Weights, Values, Max_Index),
         Den_R => Sum_Weight (Weights),
         Num_A => Weighted_Sum_Abs_Rec (Weights, Values, Max_Index));
   end Error_For_Sum;

   procedure Precise_Bounds_For_Sum
     (Weights : Weight_Array;
      Values  : Value_Array)
   is
      --  Lemma: Prove by induction that Sum_Weight is either 0.0 or more than
      --         Min_Weight on real numbers

      procedure Min_Bound_For_SW (I : Extended_Index) with
        Subprogram_Variant => (Decreases => I),
        Post => Sum_Weight_Rec (Weights, I) = Big_Real'(0.0)
        or else Sum_Weight_Rec (Weights, I) >= To_Big_Real (Min_Weight)
      is
      begin
         if I /= 0 then
            Min_Bound_For_SW (I - 1);
         end if;
      end Min_Bound_For_SW;

   begin
      --  Sum_Weight (Weights) in floats is not 0.0
      Error_For_SW (Weights);
      --  Compute the error for the computation of Weighted_Sum
      Error_For_Sum (Weights, Values);
      --  Bound Weighted_Sum and Weighted_Sum_Abs by Max_Value on real numbers
      Sum_Less_Than_Sum_Abs (Weights, Values, Max_Index);
      Bound_Sum_Abs (Weights, Values, Max_Index);
      pragma Assert (Weighted_Sum_Abs (Weights, Values) <= To_Big_Real (Max_Value));
      --  Sum_Weight is more than Min_Weight on real numbers
      Min_Bound_For_SW (Max_Index);
      pragma Assert (Sum_Weight (Weights) >= To_Big_Real (Min_Weight));

      --  Compute the most precise bound for Weighted_Sum on floats given by
      --  the error bound on the computation and the bound on real numbers.
      pragma Assert
        (abs (To_Big_Real (Float'(Weighted_Sum (Weights, Values)))) <=
           To_Big_Real (Max_Value) + 1.25E-45 + 2.52E-43 / To_Big_Real (Min_Weight)
         + 2.05E-5 * To_Big_Real (Max_Value));
   end Precise_Bounds_For_Sum;

end Libst.Reals.Errors;
