with SPARK.Lemmas.Mod32_Arithmetic; use SPARK.Lemmas.Mod32_Arithmetic;
with Interfaces; use Interfaces;

procedure Test_Arith with
  SPARK_Mode
is
   subtype Small_Natural is Unsigned_32 range 0 .. 10_000;
   subtype Small_Positive is Unsigned_32 range 1 .. 10_000;
   subtype Positive_32 is Unsigned_32 range 1 .. Unsigned_32'Last;

   --  Bitwise and

   procedure And_Idempotent (X : Unsigned_32; R : out Unsigned_32) with
     Post => R = X
   is
   begin
      R := X and X;
   end And_Idempotent;

   procedure And_Unit (X : Unsigned_32; R : out Unsigned_32) with
     Post => R = X
   is
   begin
      R := X and Unsigned_32'Last;
   end And_Unit;

   procedure And_Bound (X, Y, Z : Unsigned_32; R : out Unsigned_32) with
     Pre  => X <= Z or Y <= Z,
     Post => R <= Z
   is
   begin
      R := X and Y;
   end And_Bound;

   --  Bitwise or

   procedure Or_Idempotent (X : Unsigned_32; R : out Unsigned_32) with
     Post => R = X
   is
   begin
      R := X or X;
   end Or_Idempotent;

   procedure Or_Unit (X : Unsigned_32; R : out Unsigned_32) with
     Post => R = X
   is
   begin
      R := X or 0;
   end Or_Unit;

   procedure Or_Bound (X, Y, Z : Unsigned_32; R : out Unsigned_32) with
     Pre  => X >= Z or Y >= Z,
     Post => R >= Z
   is
   begin
      R := X or Y;
   end Or_Bound;

   --  Multiplication

   procedure Mult_Zero (X, Y : Unsigned_32; R : out Unsigned_32) with
     Pre => X = 0 or Y = 0,
     Post => R = 0
   is
   begin
      R := X * Y;
   end Mult_Zero;

   procedure Mult_Non_Zero (X, Y : Small_Positive; R : out Unsigned_32) with
     Post => R >= X and R >= Y
   is
   begin
      R := X * Y;
   end Mult_Non_Zero;

   procedure Mult_Is_Zero (X, Y : Small_Natural; R : out Unsigned_32) with
     Post => (if R = 0 then X = 0 or Y = 0)
   is
   begin
      R := X * Y;
   end Mult_Is_Zero;

   procedure Mult_Is_Monotonic (X1, X2, Y : Small_Natural; R1, R2 : out Unsigned_32) with
     Pre => X1 <= X2,
     Post => R1 <= R2
   is
   begin
      R1 := X1 * Y;
      R2 := X2 * Y;
      Lemma_Mult_Is_Monotonic (X1, X2, Y);
   end Mult_Is_Monotonic;

   procedure Mult_Is_Strictly_Monotonic (X1, X2 : Small_Natural; Y : Small_Positive; R1, R2 : out Unsigned_32) with
     Pre => X1 < X2,
     Post => R1 < R2
   is
   begin
      R1 := X1 * Y;
      R2 := X2 * Y;
      Lemma_Mult_Is_Strictly_Monotonic (X1, X2, Y);
   end Mult_Is_Strictly_Monotonic;

   procedure Mult_By_Scale (X, Y : Small_Natural; Z : Small_Positive; R : out Unsigned_32) with
     Pre => Y <= Z,
     Post => R in 0 .. X
   is
   begin
      R := (X * Y) / Z;
      Lemma_Mult_Scale (X, Y, Z, R);
   end Mult_By_Scale;

   procedure Mult_Over_Add (X, Y, Z : Unsigned_32; R1, R2 : out Unsigned_32) with
     Post => R1 = R2
   is
   begin
      R1 := (X + Y) * Z;
      R2 := X * Z + Y * Z;
   end Mult_Over_Add;

   --  Division

   procedure Div_By_2 (X, Y : Unsigned_32; R : out Unsigned_32) with
     Pre => X in 1 .. 100 and Y in 1 .. 100 and X <= Y,
     Post => R in X .. Y
   is
   begin
      R := (X + Y) / 2;
   end Div_By_2;

   procedure Div_Is_Zero (X : Small_Natural; Y : Small_Positive; R : out Unsigned_32) with
     Post => (if R = 0 then X < Y)
   is
   begin
      R := X / Y;
   end Div_Is_Zero;

   procedure Div_Is_Monotonic (X1, X2 : Small_Natural; Y : Small_Positive; R1, R2 : out Unsigned_32) with
     Pre => X1 < X2,
     Post => R1 <= R2
   is
   begin
      R1 := X1 / Y;
      R2 := X2 / Y;
      Lemma_Div_Is_Monotonic (X1, X2, Y);
   end Div_Is_Monotonic;

   --  Multiplication and division

   procedure Mult_Then_Div (X, Y : Small_Positive; R : out Unsigned_32) with
     Post => R = X
   is
   begin
      R := (X * Y) / Y;
      Lemma_Mult_Then_Div_Is_Ident (X, Y);
   end Mult_Then_Div;

   procedure Div_Then_Mult (X : Unsigned_32; Y : Small_Positive; R : out Unsigned_32) with
     Post => (if X < Y Then
                R in 0 .. X
              else
                R in X - Y + 1 .. X)
   is
   begin
      R := (X / Y) * Y;
      Lemma_Div_Then_Mult_Bounds (X, Y, R);
   end Div_Then_Mult;

   procedure Protect_Mult (X : Unsigned_32; Y : Positive_32; Z : Unsigned_32; R : out Unsigned_32) with
     Pre  => X <= Z / Y,
     Post => R <= Z
   is
   begin
      Lemma_Mult_Protect (X, Y, Z);
      R := X * Y;
   end Protect_Mult;

   --  Modulo

   procedure Mod_Range (X, Y : Small_Natural; R : out Unsigned_32) with
     Pre  => Y /= 0,
     Post => R < Y
   is
   begin
      R := X mod Y;
   end Mod_Range;

   procedure Mod_Sign (X, Y : Small_Natural; R : out Unsigned_32) with
     Pre  => Y /= 0,
     Post => R >= 0
   is
   begin
      R := X mod Y;
   end Mod_Sign;

   procedure Mult_For_Mod (X, Y : Small_Natural; R : out Unsigned_32) with
     Pre  => Y /= 0,
     Post => R mod Y = 0
   is
   begin
      R := X * Y;
      Lemma_Mult_Then_Mod_Is_Zero (X, Y);
   end Mult_For_Mod;

   X, Y, Z, R, S : Unsigned_32;

begin
   X := 23456;
   And_Idempotent (X, R);

   X := 23456;
   And_Unit (X, R);

   X := 23456;
   Y := 234;
   Z := 561;
   And_Bound (X, Y, Z, R);

   X := 23456;
   Or_Idempotent (X, R);

   X := 23456;
   Or_Unit (X, R);

   X := 23456;
   Y := 234;
   Z := 561;
   Or_Bound (X, Y, Z, R);

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
   Y := 234;
   Z := 2;
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

   X := 2356;
   Y := 45;
   Mod_Range (X, Y, R);

   X := 2356;
   Y := 45;
   Mod_Sign (X, Y, R);

   X := 2356;
   Y := 45;
   Mult_For_Mod (X, Y, R);

end Test_Arith;
