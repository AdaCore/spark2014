with SPARK.Lemmas.Integer_Arithmetic; use SPARK.Lemmas.Integer_Arithmetic;

procedure Test_Arith with
  SPARK_Mode
is
   subtype Small_Integer is Integer range -10_000 .. 10_000;
   subtype Small_Natural is Integer range 0 .. 10_000;
   subtype Small_Positive is Integer range 1 .. 10_000;

   type Sign_T is (Neg, Zero, Pos);
   function Sign (X : Integer) return Sign_T is
      (if X < 0 then Neg elsif X = 0 then Zero else Pos);

   --  Multiplication

   procedure Mult_Zero (X, Y : Integer; R : out Integer) with
     Pre => X = 0 or Y = 0,
     Post => R = 0
   is
   begin
      R := X * Y;
   end Mult_Zero;

   procedure Mult_Non_Zero (X, Y : Small_Positive; R : out Integer) with
     Post => R >= X and R >= Y
   is
   begin
      R := X * Y;
   end Mult_Non_Zero;

   procedure Mult_Is_Zero (X, Y : Small_Integer; R : out Integer) with
     Post => (if R = 0 then X = 0 or Y = 0)
   is
   begin
      R := X * Y;
   end Mult_Is_Zero;

   procedure Mult_Is_Monotonic (X1, X2, Y : Small_Natural; R1, R2 : out Integer) with
     Pre => X1 <= X2,
     Post => R1 <= R2
   is
   begin
      R1 := X1 * Y;
      R2 := X2 * Y;
   end Mult_Is_Monotonic;

   procedure Mult_Is_Strictly_Monotonic (X1, X2 : Small_Natural; Y : Small_Positive; R1, R2 : out Integer) with
     Pre => X1 < X2,
     Post => R1 < R2
   is
   begin
      R1 := X1 * Y;
      R2 := X2 * Y;
   end Mult_Is_Strictly_Monotonic;

   procedure Mult_By_Scale (X, Y : Small_Natural; Z : Small_Positive; R : out Integer) with
     Pre => Y <= Z,
     Post => R in 0 .. X
   is
   begin
      R := (X * Y) / Z;
      Lemma_Mult_Scale (X, Y, Z, R);
   end Mult_By_Scale;

   procedure Mult_Over_Add (X, Y, Z : Small_Integer; R1, R2 : out Integer) with
     Post => R1 = R2
   is
   begin
      R1 := (X + Y) * Z;
      R2 := X * Z + Y * Z;
   end Mult_Over_Add;

   --  Division

   procedure Div_By_2 (X, Y : Integer; R : out Integer) with
     Pre => X in 1 .. 100 and Y in 1 .. 100 and X <= Y,
     Post => R in X .. Y
   is
   begin
      R := (X + Y) / 2;
   end Div_By_2;

   procedure Div_Is_Zero (X : Small_Integer; Y : Small_Positive; R : out Integer) with
     Post => (if R = 0 then X < abs (Y))
   is
   begin
      R := X / Y;
   end Div_Is_Zero;

   procedure Div_Is_Monotonic (X1, X2 : Small_Natural; Y : Small_Positive; R1, R2 : out Integer) with
     Pre => X1 < X2,
     Post => R1 <= R2
   is
   begin
      R1 := X1 / Y;
      R2 := X2 / Y;
      Lemma_Div_Is_Monotonic (X1, X2, Y);
   end Div_Is_Monotonic;

   --  Multiplication and division

   procedure Mult_Then_Div (X, Y : Small_Positive; R : out Integer) with
     Post => R = X
   is
   begin
      R := (X * Y) / Y;
   end Mult_Then_Div;

   procedure Div_Then_Mult (X : Natural; Y : Small_Positive; R : out Integer) with
     Post => R in X - Y + 1 .. X
   is
   begin
      R := (X / Y) * Y;
   end Div_Then_Mult;

   procedure Protect_Mult (X : Natural; Y : Positive; Z : Natural; R : out Integer) with
     Pre  => X <= Z / Y,
     Post => R <= Z
   is
   begin
      Lemma_Mult_Protect (X, Y, Z);
      R := X * Y;
   end Protect_Mult;

   --  Modulo

   procedure Mod_Range (X, Y : Small_Integer; R : out Integer) with
     Pre  => Y /= 0,
     Post => abs (R) < abs (Y)
   is
   begin
      R := X mod Y;
      if Y > 0 then
         Lemma_Mod_Range (X, Y);
      else
         Lemma_Mod_Symmetry (X, Y);
         Lemma_Mod_Range (-X, -Y);
      end if;
   end Mod_Range;

   procedure Mod_Sign (X, Y : Small_Integer; R : out Integer) with
     Pre  => Y /= 0,
     Post => (if R /= 0 then Sign (R) = Sign (Y))
   is
   begin
      R := X mod Y;
   end Mod_Sign;

   procedure Mod_Symmetrical (X, Y : Small_Integer; R1, R2 : out Integer) with
     Pre  => Y /= 0,
     Post => R1 = - R2
   is
   begin
      R1 := X mod Y;
      R2 := (-X) mod (-Y);
      Lemma_Mod_Symmetry (X, Y);
   end Mod_Symmetrical;

   procedure Mult_For_Mod (X, Y : Small_Integer; R : out Integer) with
     Pre  => Y /= 0,
     Post => R mod Y = 0
   is
   begin
      R := X * Y;
      if Y > 0 then
         Lemma_Mult_Then_Mod_Is_Zero (X, Y);
      else
         Lemma_Mult_Then_Mod_Is_Zero (X, -Y);
         Lemma_Mod_Symmetry (R, Y);
      end if;
   end Mult_For_Mod;

   --  Exponentiation

   subtype Very_Small_Natural is Integer range 0 .. 50;
   subtype Very_Small_Positive is Integer range 1 .. 50;

   subtype Very_Very_Small_Natural is Integer range 0 .. 5;

   procedure Exp_Is_Monotonic (X1, X2 : Very_Small_Natural; E : Very_Very_Small_Natural; R1, R2 : out Integer) with
     Pre => X1 < X2,
     Post => R1 <= R2
   is
   begin
      R1 := X1 ** E;
      R2 := X2 ** E;
      Lemma_Exp_Is_Monotonic (X1, X2, E);
   end Exp_Is_Monotonic;

   procedure Exp_Is_Monotonic_2 (X : Very_Small_Positive; E1, E2 : Very_Very_Small_Natural; R1, R2 : out Integer) with
     Pre => E1 < E2,
     Post => R1 <= R2
   is
   begin
      R1 := X ** E1;
      R2 := X ** E2;
      Lemma_Exp_Is_Monotonic_2 (X, E1, E2);
   end Exp_Is_Monotonic_2;

   X, Y, Z, R, S : Integer;


begin
   X := 0;
   Y := 1;
   Mult_Zero (X, Y, R);

   X := 1;
   Y := 1;
   Mult_Non_Zero (X, Y, R);

   X := 0;
   Y := 1;
   Mult_Is_Zero (X, Y, R);
   X := 1;
   Y := 1;
   Mult_Is_Zero (X, Y, R);

   X := 45;
   Y := 234;
   Mult_Is_Monotonic (X, X + 34, Y, R, S);

   X := 45;
   Y := 234;
   Mult_Is_Strictly_Monotonic (X, X + 34, Y, R, S);

   X := 45;
   Y := 234;
   Mult_By_Scale (X, Y, Y + 1, R);

   X := 45;
   Y := -234;
   Z := -2;
   Mult_Over_Add (X, Y, Z, R, S);

   X := 24;
   Y := 45;
   Div_By_2 (X, Y, R);

   X := 45;
   Y := 24;
   Div_Is_Zero (X, Y, R);
   X := 24;
   Y := 45;
   Div_Is_Zero (X, Y, R);

   X := 24;
   Y := 45;
   Z := 3;
   Div_Is_Monotonic (X, Y, Z, R, S);

   X := 24;
   Y := 45;
   Mult_Then_Div (X, Y, R);

   X := 24;
   Y := 45;
   Div_Then_Mult (X, Y, R);

   X := 24;
   Y := 45;
   Z := 2046;
   Protect_Mult (X, Y, Z, R);

   X := -2356;
   Y := -45;
   Mod_Range (X, Y, R);

   X := -2356;
   Y := -45;
   Mod_Sign (X, Y, R);

   X := -2356;
   Y := -45;
   Mod_Symmetrical (X, Y, R, S);

   X := -2356;
   Y := -45;
   Mult_For_Mod (X, Y, R);

   X := 38;
   Y := 40;
   Z := 3;
   Exp_Is_Monotonic (X, Y, Z, R, S);

   X := 38;
   Y := 1;
   Z := 5;
   Exp_Is_Monotonic_2 (X, Y, Z, R, S);

end Test_Arith;
