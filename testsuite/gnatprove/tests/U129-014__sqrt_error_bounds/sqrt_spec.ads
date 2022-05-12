with Ada.Numerics.Big_Numbers.Big_Reals; use Ada.Numerics.Big_Numbers.Big_Reals;
with Ada.Numerics.Elementary_Functions; use Ada.Numerics.Elementary_Functions;
package Sqrt_Spec with
  Ghost,
  SPARK_Mode
is
   package Float_Conversions is new
     Ada.Numerics.Big_Numbers.Big_Reals.Float_Conversions (Float);
   use Float_Conversions;
   --  Conversions between Big_Real and Float

   Epsilon      : constant := 1.0E-7;
   pragma Assert (2.0 ** (-24) <= Epsilon);
   --  Over-approximation of the machine epsilon for 32bits floats
   First_Norm   : constant := 1.2E-38;
   pragma Assert (2.0 ** (-126) <= First_Norm);
   --  Over-approximation of the first positive normal number
   Error_Denorm : constant := 1.0E-45;
   pragma Assert (2.0 ** (-150) <= Error_Denorm);
   --  Over-approximation of the error bound on denormal numbers

   Sqrt_Bound   : constant := 1.0E-8;
   --  Small enough value to be absorbed by the over-approximation on Epsilon
   --  and Error_Denorm.
   Sq_Bound     : constant := 1.999 * Sqrt_Bound;
   --  Approximation of the minimum bound on the square to ensure Sqrt_Bound on
   --  the sqrt.

   procedure Lemma_Sqrt_Bounds (X, Y : Valid_Big_Real) with
     Pre  => X >= 0.0 and Y >= 0.0
       and abs (X * X - Y * Y) <= Big_Real'(Sq_Bound) * Y * Y,
     Post => abs (X - Y) <= Big_Real'(Sqrt_Bound) * Y;
   --  Sq_Bound is a safe approximation for Sqrt_Bound

   function Sqrt (X : Big_Real) return Big_Real with
     Import,
     Pre  => X >= 0.0,
     Post => Sqrt'Result >= 0.0
     and then abs (X - Sqrt'Result * Sqrt'Result)
       <= Big_Real'(Sq_Bound) * Sqrt'Result * Sqrt'Result;
   --  Approximation of sqrt on real numbers

   --  It is the error bound due to the the approximation of the real value of
   --  Sqrt is small enough to be absorbed in the over-approximations on
   --  Epsilon and Error_Denorm.
   pragma Assert (Sqrt_Bound + 2.0 ** (-24) <= Epsilon);
   pragma Assert (Sqrt_Bound * First_Norm + 2.0 ** (-150) <= Error_Denorm);

   --  Axiom: Error bound for Sqrt
   procedure Bound_Error_Sqrt (X : Float) with
     Import,
     Pre  => X >= 0.0,
     Post => abs (To_Big_Real (Sqrt (X)) - Sqrt (To_Big_Real (X))) <=
       (if Sqrt (To_Big_Real (X)) >= Big_Real'(First_Norm)
        then Big_Real'(Epsilon) * Sqrt (To_Big_Real (X))
        else Big_Real'(Error_Denorm));

   --  Axiom: Sqrt is monotonic
   procedure Sqrt_Is_Monotonic (X, Y : Float) with
     Import,
     Pre  => X >= 0.0 and Y >= X,
     Post => Sqrt (Y) >= Sqrt (X);

   --  Axiom: Sqrt is exact on squares of integers in the range where all
   --  integers are representible.
   procedure Sqrt_Exact_Integer (X : Integer) with
     Import,
     Pre  => X in 0 .. 2896,
     Post => Sqrt (Float (X) ** 2) = Float (X);
end Sqrt_Spec;
