with SPARK.Lemmas.Integer_Arithmetic; use SPARK.Lemmas.Integer_Arithmetic;

procedure Mul_Lemmas with
  SPARK_Mode
is
   pragma Warnings (Off, "postcondition does not check the outcome of calling");

   subtype Small_Integer is Integer range -1_000 .. 1_000;
   subtype Small_Natural is Integer range 0 .. 1_000;
   subtype Small_Positive is Integer range 1 .. 1_000;

   type Sign_T is (Neg, Zero, Pos);
   function Sign (X : Integer) return Sign_T is
      (if X < 0 then Neg elsif X = 0 then Zero else Pos);

   procedure Mul_Strictly_Positive (X, Y : Small_Positive; Res : out Integer) with
     Post => Res > 0
   is
   begin
      Res := X * Y;
   end Mul_Strictly_Positive;

   procedure Mul_Nonzero (X, Y : Small_Integer; Res : out Integer) with
     Post => (if Res /= 0 then X /= 0 and Y /= 0)
   is
   begin
      Res := X * Y;
   end Mul_Nonzero;

   procedure Mul_Is_Associative (X, Y, Z : Small_Integer; Res1, Res2 : out Integer) with
     Post => Res1 = Res2
   is
   begin
      Res1 := X * (Y * Z);
      Res2 := (X * Y) * Z;
   end Mul_Is_Associative;

  procedure Mul_Is_Distributive_Add (X, Y, Z : Small_Integer; Res1, Res2 : out Integer) with
     Post => Res1 = Res2
   is
   begin
      Res1 := X * (Y + Z);
      Res2 := X * Y + X * Z;
   end Mul_Is_Distributive_Add;

   procedure Mul_Ordering (X, Y : Small_Positive; Res : out Integer) with
     Post => X <= Res and then Y <= Res
   is
   begin
      Res := X * Y;
   end Mul_Ordering;

  procedure Mul_Strict_Inequality (X, Y: Small_Integer; Z : Small_Positive; Res1, Res2 : out Integer) with
     Pre  => X < Y,
     Post => Res1 < Res2
   is
   begin
      Res1 := X * Z;
      Res2 := Y * Z;
   end Mul_Strict_Inequality;

  procedure Mul_Inequality (X, Y: Small_Integer; Z : Small_Positive; Res1, Res2 : out Integer) with
     Pre  => X <= Y,
     Post => Res1 <= Res2
   is
   begin
      Res1 := X * Z;
      Res2 := Y * Z;
   end Mul_Inequality;

  procedure Mul_Upper_Bound (X, X_Bound, Y, Y_Bound: Small_Natural; Res1, Res2 : out Integer) with
     Pre  => X <= X_Bound and then Y <= Y_Bound,
     Post => Res1 <= Res2
   is
   begin
      Res1 := X * Y;
      Res2 := X_Bound * Y_Bound;
   end Mul_Upper_Bound;

  procedure Mul_Strict_Upper_Bound (X, X_Bound, Y, Y_Bound: Small_Natural; Res1, Res2 : out Integer) with
     Pre  => X < X_Bound and then Y < Y_Bound,
     Post => Res1 < Res2
   is
   begin
      Res1 := X * Y;
      Res2 := X_Bound * Y_Bound;
   end Mul_Strict_Upper_Bound;

   procedure Mul_Left_Inequality (X : Small_Positive; Y, Z: Small_Integer; Res1, Res2 : out Integer) with
     Post => (if Y <= Z then Res1 <= Res2) and then
             (if Y < Z then Res1 < Res2)
   is
   begin
      Res1 := X * Y;
      Res2 := X * Z;
   end Mul_Left_Inequality;

   procedure Mul_Strict_Inequality_Converse (X, Y : Small_Integer; Z: Small_Natural) with
     Global => null,
     Pre  => X * Z < Y * Z,
     Post => X < Y
   is
   begin
      null;
   end Mul_Strict_Inequality_Converse;

   procedure Mul_Inequality_Converse (X, Y : Small_Integer; Z: Small_Positive) with
     Global => null,
     Pre  => X * Z <= Y * Z,
     Post => X <= Y
   is
   begin
      null;
   end Mul_Inequality_Converse;

   procedure Mul_Equality_Converse (X, Y : Small_Integer; Z: Small_Positive) with
     Global => null,
     Pre  => X * Z = Y * Z,
     Post => X = Y
   is
   begin
      null;
   end Mul_Equality_Converse;

   procedure Mul_Strictly_Increases (X : Small_Integer; Y: Small_Positive; Res : out Integer) with
     Pre  => 1 < X,
     Post => Y < Res
   is
   begin
      Res := X * Y;
   end Mul_Strictly_Increases;

   procedure Mul_Increases (X, Y: Small_Positive; Res : out Integer) with
     Post => Y <= Res
   is
   begin
      Res := X * Y;
   end Mul_Increases;

   procedure Mul_Nonnegative (X, Y: Small_Natural; Res : out Integer) with
     Post => 0 <= Res
   is
   begin
      Res := X * Y;
   end Mul_Nonnegative;

   procedure Mul_Unary_Negation (X, Y: Small_Integer; Res1, Res2, Res3 : out Integer) with
     Post => Res1 = Res2 and then Res2 = Res3
   is
   begin
      Res1 := (-X) * Y;
      Res2 := - (X * Y);
      Res3 := X * (-Y);
   end Mul_Unary_Negation;

   procedure Mul_One_To_One (M, X, Y: Small_Integer) with
     Global => null,
     Pre  => M /= 0 and then M * X = M * Y,
     Post => X = Y
   is
   begin
      null;
   end Mul_One_To_One;

   procedure Mul_Cancels_Negatives (X, Y: Small_Natural; Res1, Res2 : out Integer) with
     Post => Res1 = Res2
   is
   begin
      Res1 := X * Y;
      Res2 := (-X) * (-Y);
   end Mul_Cancels_Negatives;

   X, Y, Z, R, S : Integer;

begin
   X := 4;
   Y := 827;
   Mul_Strictly_Positive (X, Y, R);

   X := 4;
   Y := 827;
   Mul_Nonzero (X, Y, R);

   X := 4;
   Y := 827;
   Z := 827;
   Mul_Is_Associative (X, Y, Z, R, S);

   X := 4;
   Y := 827;
   Z := 827;
   Mul_Is_Distributive_Add (X, Y, Z, R, S);

   X := 4;
   Y := 827;
   Mul_Ordering (X, Y, R);

   X := 4;
   Y := 827;
   Z := 827;
   Mul_Strict_Inequality (X, Y, Z, R, S);

   X := 4;
   Y := 827;
   Z := 827;
   Mul_Inequality (X, Y, Z, R, S);

   X := 4;
   Y := 827;
   Mul_Upper_Bound (X, X + 34, Y, Y + 123, R, S);

   X := 4;
   Y := 827;
   Mul_Strict_Upper_Bound (X, X + 34, Y, Y + 123, R, S);

   X := 4;
   Y := 827;
   Z := 827;
   Mul_Left_Inequality (X, Y, Z, R, S);

   X := 4;
   Y := 827;
   Z := 827;
   Mul_Strict_Inequality_Converse (X, Y, Z);

   X := 4;
   Y := 827;
   Z := 827;
   Mul_Inequality_Converse (X, Y, Z);

   X := 4;
   Y := 4;
   Z := 827;
   Mul_Equality_Converse (X, Y, Z);

   X := 4;
   Y := 4;
   Mul_Strictly_Increases (X, Y, R);

   X := 4;
   Y := 4;
   Mul_Increases (X, Y, R);

   X := 4;
   Y := 4;
   Mul_Nonnegative (X, Y, R);

   X := 4;
   Y := 4;
   Mul_Unary_Negation (X, Y, Z, R, S);

   X := 4;
   Y := 4;
   Mul_One_To_One (345, X, Y);

   X := 4;
   Y := 4;
   Mul_Cancels_Negatives (X, Y, R, S);

end Mul_Lemmas;
