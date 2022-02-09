package body Norm.Reals.Errors with SPARK_Mode is

   --  Types for which the floating point operations are safe

   subtype Floats_For_Add is Float range Float'First / 2.0 .. Float'Last / 2.0;
   subtype Floats_For_Mul is Float range - Float_Sqrt .. Float_Sqrt;

   --  Lemmas giving an error bound for each binary operator

   procedure Bound_Error_Add (X, Y : Floats_For_Add) with
     Post => abs (To_Big_Real (X + Y) - (To_Big_Real (X) + To_Big_Real (Y))) <=
       (if abs (To_Big_Real (X) + To_Big_Real (Y)) >= Big_Real'(First_Norm)
        then Big_Real'(Epsilon) * abs (To_Big_Real (X) + To_Big_Real (Y))
        else Big_Real'(Error_Denorm));
   procedure Bound_Error_Add (X, Y : Floats_For_Add) is null;
   procedure Bound_Error_Mul (X, Y : Floats_For_Mul) with
     Post => abs (To_Big_Real (X * Y) - To_Big_Real (X) * To_Big_Real (Y)) <=
       (if abs (To_Big_Real (X) * To_Big_Real (Y)) >= Big_Real'(First_Norm)
        then Big_Real'(Epsilon) * abs (To_Big_Real (X) * To_Big_Real (Y))
        else Big_Real'(Error_Denorm));
   procedure Bound_Error_Mul (X, Y : Floats_For_Mul) is null;

   --  Proofs of error bound lemmas on our specification

   procedure Error_For_Sum_Rec
     (Values : Value_Array;
      I      : Index)
   is

      --  Lemma: The summation up to I - 1 can be used inside additions

      procedure Bound_Weighted_Sum (Sum : Float) with
        Pre  => Sum in 0.0 .. Max_Value ** 2 * Float (I - 1),
        Post => Sum in Floats_For_Add;
      procedure Bound_Weighted_Sum (Sum : Float) is null;

      --  Lemma: Lift the error bound on the top-level addition so that it is
      --     expressed in terms of the real function.

      procedure Lift_Bounds
        (Sum_F : Floats_For_Add;
         V     : Floats_For_Mul;
         Sum_R : Valid_Big_Real)
      with
        Pre => I /= 1 and Sum_R >= 0.0
        and abs (To_Big_Real (Sum_F) - Sum_R)
          <= 2.5E-45 * To_Real (I - 1) + (1.0E-7 + 1.01E-7 * To_Real (I - 2)) * Sum_R
        and abs (To_Big_Real (Sum_F + V ** 2) - (To_Big_Real (Sum_F) + To_Big_Real (V ** 2)))
          <= 1.2E-45 + 1.0E-7 * (To_Big_Real (Sum_F) + To_Big_Real (V ** 2))
        and abs (To_Big_Real (V ** 2) - (To_Big_Real (V) * To_Big_Real (V)))
          <= 1.2E-45 + 1.0E-7 * To_Big_Real (V) * To_Big_Real (V),
        Post => abs (To_Big_Real (Sum_F + V ** 2) - (To_Big_Real (Sum_F) + To_Big_Real (V ** 2)))
          <= 1.21E-45 + 1.01E-7 * Sum_R + 1.01E-7 * To_Big_Real (V) * To_Big_Real (V);
      procedure Lift_Bounds
        (Sum_F : Floats_For_Add;
         V     : Floats_For_Mul;
         Sum_R : Valid_Big_Real)
      is
      begin
         pragma Assert
           (abs (To_Big_Real (Sum_F + V ** 2) - (To_Big_Real (Sum_F) + To_Big_Real (V ** 2))) <=
              1.205E-45 + 1.01E-7 * Sum_R + 1.0E-7 * To_Big_Real (V ** 2));
      end Lift_Bounds;

      --  Lemma: Aggregate together error bounds coming from:
      --    * The computation of the summation up to I - 1
      --    * The last addition
      --    * The nested multiplication

      procedure Aggregate_Bounds
        (Sum_F : Floats_For_Add;
         V     : Floats_For_Mul;
         Sum_R : Valid_Big_Real)
      with
        Pre => I /= 1 and Sum_R >= 0.0
        and abs (To_Big_Real (Sum_F) - Sum_R)
          <= 2.5E-45 * To_Real (I - 1) + (1.0E-7 + 1.01E-7 * To_Real (I - 2)) * Sum_R
        and abs (To_Big_Real (Sum_F + V ** 2) - (To_Big_Real (Sum_F) + To_Big_Real (V ** 2)))
          <= 1.21E-45 + 1.01E-7 * Sum_R + 1.01E-7 * To_Big_Real (V) * To_Big_Real (V)
        and abs (To_Big_Real (V ** 2) - (To_Big_Real (V) * To_Big_Real (V)))
          <= 1.2E-45 + 1.0E-7 * To_Big_Real (V) * To_Big_Real (V),
        Post => abs (To_Big_Real (Sum_F + V ** 2) - (Sum_R + To_Big_Real (V) * To_Big_Real (V)))
          <= 2.5E-45 * To_Real (I) + (1.0E-7 + 1.01E-7 * To_Real (I - 1))
           * (Sum_R + To_Big_Real (V) * To_Big_Real (V));
      procedure Aggregate_Bounds
        (Sum_F : Floats_For_Add;
         V     : Floats_For_Mul;
         Sum_R : Valid_Big_Real) is null;

      --  Lemma: The prostcondition gives a correct error bound when I is 1

      procedure Prove_Post_First
        (Sum_F, Pre_F : Floats_For_Add;
         V            : Floats_For_Mul;
         Sum_R, Pre_R : Valid_Big_Real)
      with
        Pre  => Sum_F = V ** 2 + Pre_F
          and Sum_R = To_Big_Real (V) * To_Big_Real (V) + Pre_R
          and Pre_F = 0.0 and Pre_R = 0.0
          and abs (To_Big_Real (V ** 2) - To_Big_Real (V) * To_Big_Real (V))
          <= 1.2E-45 + 1.0E-7 * To_Big_Real (V) * To_Big_Real (V),
        Post => abs (To_Big_Real (Sum_F) - Sum_R)
          <= 2.5E-45 * To_Real (I) + (1.0E-7 + 1.01E-7 * To_Real (I - 1)) * Sum_R;
      procedure Prove_Post_First
        (Sum_F, Pre_F : Floats_For_Add;
         V            : Floats_For_Mul;
         Sum_R, Pre_R : Valid_Big_Real) is null;

      --  Lemma: The prostcondition gives a correct error bound when I is more
      --     than 1.

      procedure Prove_Post
        (Sum_F, Pre_F : Floats_For_Add;
         V            : Floats_For_Mul;
         Sum_R, Pre_R : Valid_Big_Real)
      with
        Pre  => Sum_F = V ** 2 + Pre_F and Sum_R = To_Big_Real (V) * To_Big_Real (V) + Pre_R
        and abs (To_Big_Real (V ** 2 + Pre_F) - (To_Big_Real (V) * To_Big_Real (V) + Pre_R))
          <= 2.5E-45 * To_Real (I) + (1.0E-7 + 1.01E-7 * To_Real (I - 1))
           * (To_Big_Real (V) * To_Big_Real (V) + Pre_R),
        Post => abs (To_Big_Real (Sum_F) - Sum_R)
          <= 2.5E-45 * To_Real (I) + (1.0E-7 + 1.01E-7 * To_Real (I - 1)) * Sum_R;
      procedure Prove_Post
        (Sum_F, Pre_F : Floats_For_Add;
         V            : Floats_For_Mul;
         Sum_R, Pre_R : Valid_Big_Real) is null;

   begin
      --  Compute the error for the multiplication
      Bound_Error_Mul (Values (I), Values (I));
      if I = 1 then
         --  The prostcondition gives a correct error bound
         Prove_Post_First
           (Sum_F => Sum_Of_Squares_Rec (Values, I),
            Pre_F => Sum_Of_Squares_Rec (Values, I - 1),
            V     => Values (I),
            Sum_R => Sum_Of_Squares_Rec (Values, I),
            Pre_R => Sum_Of_Squares_Rec (Values, I - 1));
      else
         --  The summation up to I - 1 can be used inside additions
         Bound_Weighted_Sum (Sum_Of_Squares_Rec (Values, I - 1));
         --  Compute the error for the summation up to I - 1
         Error_For_Sum_Rec (Values, I - 1);
         --  Compute the error for the last addition
         Bound_Error_Add
           (Sum_Of_Squares_Rec (Values, I - 1), Values (I) ** 2);
         --  Lift the error bound on the top-level addition so that it is
         --  expressed in terms of the real function.
         Lift_Bounds
           (Sum_F => Sum_Of_Squares_Rec (Values, I - 1),
            V     => Values (I),
            Sum_R => Sum_Of_Squares_Rec (Values, I - 1));
         --  Aggregate together error bounds coming from all the computations
         Aggregate_Bounds
           (Sum_F => Sum_Of_Squares_Rec (Values, I - 1),
            V     => Values (I),
            Sum_R => Sum_Of_Squares_Rec (Values, I - 1));
         --  The prostcondition gives a correct error bound
         Prove_Post
           (Sum_F => Sum_Of_Squares_Rec (Values, I),
            Pre_F => Sum_Of_Squares_Rec (Values, I - 1),
            V     => Values (I),
            Sum_R => Sum_Of_Squares_Rec (Values, I),
            Pre_R => Sum_Of_Squares_Rec (Values, I - 1));
      end if;
   end Error_For_Sum_Rec;

   procedure Norm (Values : Value_Array) is

      --  Lemma: Compute the error bound of the square root of a computation
      --     from the error bound on the computation.
      --     It is made of 3 parts:
      --       * A part coming from the relative error E on X and Y,
      --         E / 1.999 * Sqrt (Y)
      --       * A part coming from the approximation on the computation of
      --         Sqrt on big reals, 2.0 * 1.999E-8 / 1.999 * Sqrt (Y)
      --       * A part coming from the absolute error F on X and Y,
      --         1.01 * Sqrt (F)
      --     These 3 parts are approximations at the first order. The bounds
      --     on E and F are used to ensure that the second order terms are
      --     absorbed in the approximation of the first order terms.

      procedure Lift_Sqrt (X, Y, E, F : Valid_Big_Real) with
        Pre  => X >= 0.0 and Y >= 0.0
        and E >= 0.0 and E <= 1.01E-5
        and F >= 0.0 and F <= 1.0E-5
        and abs (X - Y) <= E * Y + F,
        Post => abs (Sqrt (X) - Sqrt (Y)) <=
          (2.0 * 1.999E-8 + E) / 1.999 * Sqrt (Y) + 1.01 * Sqrt (F);

      --  Lemma: Aggregate together error bounds coming from:
      --    * The computation of the summation of the squares
      --    * The square root

      procedure Lift_Sqrt (X, Y, E, F : Valid_Big_Real) is null;

      procedure Aggregate_Bounds (Norm_F, Sqrt_F, Norm_R : Valid_Big_Real) with
        Pre  => Norm_F >= 0.0 and Norm_R >= 0.0 and Sqrt_F >= 0.0
          and abs (Norm_F - Sqrt_F) <= 1.2E-45 + 1.0E-7 * Sqrt_F
          and abs (Sqrt_F - Norm_R) <= 1.01 * Sqrt (2.5E-43) + 5.15E-6 * Norm_R,
        Post => abs (Norm_F - Norm_R) <= 5.1E-22 + 5.3E-6 * Norm_R;
      procedure Aggregate_Bounds (Norm_F, Sqrt_F, Norm_R : Valid_Big_Real) is
      null;

   begin
      Error_For_Sum_Rec (Values, Max_Index);
      Lift_Sqrt
        (X => To_Big_Real (Sum_Of_Squares_Rec (Values, Max_Index)),
         Y => Sum_Of_Squares_Rec (Values, Max_Index),
         E => 1.01E-5,
         F => 2.5E-43);
      Bound_Error_Sqrt (Sum_Of_Squares_Rec (Values, Max_Index));
      Aggregate_Bounds
        (Norm_F => To_Big_Real (Sqrt (Sum_Of_Squares_Rec (Values, Max_Index))),
         Sqrt_F => Sqrt (To_Big_Real (Sum_Of_Squares_Rec (Values, Max_Index))),
         Norm_R => Sqrt (Sum_Of_Squares_Rec (Values, Max_Index)));
   end Norm;

end Norm.Reals.Errors;
