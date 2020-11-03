with SPARK.Float_Arithmetic_Lemmas; use SPARK.Float_Arithmetic_Lemmas;

procedure Test_Arith with
  SPARK_Mode
is
   subtype Small_Float is Float range -2.0**20 .. 2.0**20;
   subtype Small_Nat_Float is Float range 0.0 .. 2.0**20;
   subtype Small_Pos_Float is Float range 1.0 .. 2.0**20;

   --  Addition

   procedure Add_Is_Monotonic (X1, X2, Y : Small_Float; R1, R2 : out Float) with
     Pre => X1 <= X2,
     Post => R1 <= R2
   is
   begin
      R1 := X1 + Y;
      R2 := X2 + Y;
      Lemma_Add_Is_Monotonic (X1, X2, Y);
   end Add_Is_Monotonic;

   --  Subtraction

   procedure Sub_Is_Monotonic (X1, X2, Y : Small_Float; R1, R2 : out Float) with
     Pre => X1 <= X2,
     Post => R1 <= R2
   is
   begin
      R1 := X1 - Y;
      R2 := X2 - Y;
      Lemma_Sub_Is_Monotonic (X1, X2, Y);
   end Sub_Is_Monotonic;

   --  Multiplication

   procedure Mult_Zero (X, Y : Float; R : out Float) with
     Pre => X = 0.0 or Y = 0.0,
     Post => R = 0.0
   is
   begin
      R := X * Y;
   end Mult_Zero;

   procedure Mult_Is_Monotonic (X1, X2 : Small_Float; Y : Small_Nat_Float; R1, R2 : out Float) with
     Pre => X1 <= X2,
     Post => R1 <= R2
   is
   begin
      R1 := X1 * Y;
      R2 := X2 * Y;
      Lemma_Mult_Is_Monotonic (X1, X2, Y);
   end Mult_Is_Monotonic;

   procedure Mult_Right_Is_Monotonic (X1, X2 : Small_Float; Y : Small_Nat_Float; R1, R2 : out Float) with
     Pre => X1 <= X2,
     Post => R2 <= R1
   is
   begin
      R1 := X1 * (-Y);
      R2 := X2 * (-Y);
      Lemma_Mult_Right_Negative_Is_Monotonic (X1, X2, (-Y));
   end Mult_Right_Is_Monotonic;

   --  Division

   procedure Div_Is_Monotonic (X1, X2 : Small_Float; Y : Small_Pos_Float; R1, R2 : out Float) with
     Pre => X1 <= X2,
     Post => R1 <= R2
   is
   begin
      R1 := X1 / Y;
      R2 := X2 / Y;
      Lemma_Div_Is_Monotonic (X1, X2, Y);
   end Div_Is_Monotonic;

   procedure Div_Right_Is_Monotonic (X1, X2 : Small_Float; Y : Small_Pos_Float; R1, R2 : out Float) with
     Pre => X1 <= X2,
     Post => R2 <= R1
   is
   begin
      R1 := X1 / (-Y);
      R2 := X2 / (-Y);
      Lemma_Div_Right_Negative_Is_Monotonic (X1, X2, (-Y));
   end Div_Right_Is_Monotonic;

   X, Y, Z, R, S : Float;

begin

   X := 0.0;
   Y := 1.0;
   Z := 42.0;

   Add_Is_Monotonic (X, Y, Z, R, S);
   Sub_Is_Monotonic (X, Y, Z, R, S);
   Mult_Zero (X, Y, R);
   Mult_Is_Monotonic (X, Y, Z, R, S);
   Mult_Right_Is_Monotonic (X, Y, Z, R, S);
   Div_Is_Monotonic (X, Y, Z, R, S);
   Div_Right_Is_Monotonic (X, Y, Z, R, S);

   pragma Assert (Is_Integer_64 (Z));
   pragma Assert (Is_Integer_32 (Z));
   pragma Assert (Is_Integer (Z));

   pragma Assert (Is_Float (Integer_64'(42)));
   pragma Assert (Is_Float (Integer_32'(42)));

end Test_Arith;
