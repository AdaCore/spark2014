package body Foo
  with SPARK_Mode
is

   ----------------------------------------------------------------------
   --  Outrageously nasty tests
   ----------------------------------------------------------------------

   function Magic (X : Float) return Integer
     with Global => null,
          Convention => C,
          Import;

   procedure Equality_Matters (A, B : Float)
     with Pre => A = B
   is
   begin
      --  true for reals
      --  true for floats using round(x op y)
      --  false for properly modelled floats
      --  false for my emulation
      pragma Assert (Magic (A) = Magic (B));
   end Equality_Matters;

   procedure A_Minimum_Of_Care_Is_Needed (A, B : Float)
   is
   begin
      --  IEEE leaves it unspecified what happens if both A and B are
      --  the two different zeros.
      --
      --  true for reals
      --  true for floats using round(x op y)
      --  false for properly modelled floats
      --  true for my emulation
      pragma Assert (Magic (Float'Min (A, B)) = Magic (Float'Min (B, A)));
   end A_Minimum_Of_Care_Is_Needed;

   ----------------------------------------------------------------------
   --  These tests aim to show the difference between reals and floats
   ----------------------------------------------------------------------

   --  For reals this is true
   --  For floats this is true
   procedure Add_Monotonic (X, Y : Float)
     with Pre => (X > 0.0 and Y > 0.0)
   is
   begin
      pragma Assert (X + Y >= X);  -- Should be true
   end Add_Monotonic;

   --  For reals this is true
   --  For floats this is false
   procedure Add_Strictly_Monotonic (X, Y : Float)
     with Pre => (X > 0.000000 and Y > 0.0)
   is
   begin
      pragma Assert (X + Y > X);  -- Should be false
   end Add_Strictly_Monotonic;

   --  For reals this is false
   --  For floats this is true
   procedure Smooth (X, Y, Z : Float)
     with Pre => (X = 1.0 and Z = 1.0000001 and X < Y and Y < Z)
   is
   begin
      pragma Assert (False);  --  Should be provable as no value for Y exists
   end Smooth;

   --  For reals this is true
   --  For floats this is false
   function Negate_Wrong (X : Float) return Float
     with Post => Negate_Wrong'Result = - X
   is
   begin
      return 0.0 - X;
   end Negate_Wrong;

   function Underflow_1 (A, B : Float) return Float
     with Pre => (A > 0.0 and B > 0.0),
          Post => Underflow_1'Result > 0.0   -- false for floats!
   is
   begin
      return A / B;
   end Underflow_1;

   --  This is not just due to rounding, this also triggers if 1.0 / a
   --  is subnormal
   function Inverse_Reciprocal (A : Float) return Float
     with Pre => A > 1.0,
          Post => Inverse_Reciprocal'Result = A  -- not generally true
   is
   begin
      return 1.0 / (1.0 / A);
   end Inverse_Reciprocal;

   function Underflow_2 (A, B : Float) return Boolean
     with Pre => A * B = 0.0,
          Post => Underflow_2'Result
   is
   begin
      return A = 0.0 or B = 0.0;   -- not true!
   end Underflow_2;

   function Underflow_3 (A, B : Float) return Float
     with Pre => A > 0.0 and B > 0.0,
          Post => Underflow_3'Result > 0.0   -- not true!
   is
   begin
      return A * B;
   end Underflow_3;

   function Sqrt_Comedy_1 (A, B, C : Float) return Boolean
     with Pre => A * A = C and B * B = C,
          Post => Sqrt_Comedy_1'Result
   is
   begin
      return A = B;  --  not true
   end Sqrt_Comedy_1;

   function Bad_Optimisation_1 (A, B : Float) return Float
     with Pre => B /= 0.0,
          Post => Bad_Optimisation_1'Result = A / B
   is
   begin
      return A * (1.0 / B);   -- I don't think so
   end Bad_Optimisation_1;

   procedure Inverse_Addition (X : Float)
   is
   begin
      pragma Assert (X + X = X - (-X));  -- probably not
   end Inverse_Addition;

   procedure Substract_Identity_1 (X, Y : Float)
     with Pre => (X >= 0.0 and Y >= 0.0)
   is
   begin
      pragma Assert ((X - Y = 0.0) = (X = Y));   --  surprisingly true
   end Substract_Identity_1;

   procedure Substract_Identity_2 (X, Y : Float)
     with Pre => (X >= 0.0 and Y >= 0.0)
   is
   begin
      pragma Assert ((X - Y) + Y = X);  -- again true, but...
   end Substract_Identity_2;

   procedure Substract_Identity_3 (X, Y : Float)
     with Pre => (X >= 0.0 and Y >= 0.0)
   is
   begin
      pragma Assert ((X + Y) - Y = X);  -- haha, false! (I hate you, Martin!)
   end Substract_Identity_3;

   procedure Underflow_4 (X : Float)
     with Pre => (X > 0.0)
   is
   begin
      pragma Assert (1.0 / X > 0.0);  -- no underflow if x is finite
   end Underflow_4;

   procedure Not_So_Associative (A, B, C : Float)
   is
   begin
      pragma Assert ((A + B) + C = A + (B + C));  -- disassociative :)
   end Not_So_Associative;

   procedure I_Like_To_Commute_To_Work (A, B : Float)
   is
   begin
      pragma Assert ((A + B) = (B + A));  -- true, as long as we don't have NaN
   end I_Like_To_Commute_To_Work;

   procedure Distributed_Fun (A, B, C : Float)
   is
   begin
      pragma Assert (A * (B + C) = (A * B) + (A * C));  -- haha, no
   end Distributed_Fun;

   ----------------------------------------------------------------------
   --  Tests showing that in SPARK you avoid many of the amusing issues
   ----------------------------------------------------------------------

   --  For reals this is true
   --  For floats this is true, in most cases (but here it is as we
   --  rule out NaN)
   procedure Equality (X : Float)
   is
   begin
      pragma Assert (X = X);  --  Should be true
   end Equality;

   --  Should not be provable for reals or floats
   procedure Introduce_NaN_1 (X, Y : Float; Z : out Float)
     with Pre => (X = 12.25 and Y = 0.0)
   is
   begin
      Z := X / Y;
   end Introduce_NaN_1;

   --  Ignoring the division check, the actual equality should be:
   --     For reals true
   --     For floats false
   procedure Introduce_NaN_2 (X, Y : Float)
     with Pre => (X = 0.0 and Y = 0.0)
   is
   begin
      pragma Assert (X / Y = X / Y);  --  should be false (ignoring
                                      --  the division checks)
   end Introduce_NaN_2;

   function Introduce_NaN_3 (X, Y : Float) return Boolean
     with Pre => X = Y
   is
   begin
      return 1.0 / X = 1.0 / Y;  --  division by zero is prevented in SPARK
   end Introduce_NaN_3;

   --  For reals this is true
   --  For floats this is true
   procedure Transitive (X, Y, Z : Float)
     with Pre => (X < Y and Y < Z)
   is
   begin
      pragma Assert (X < Z); -- Should be true
   end Transitive;

   function Exhaustive (A : Float) return Integer
   is
   begin
      if A < 0.0 then
         return -1;
      elsif A = 0.0 then
         return 0;
      else
         pragma Assert (A > 0.0);  --  not true in Ada / C for NaA
         return 1;
      end if;
   end Exhaustive;

   procedure Negation_1 (F : Float)
     with Pre => F = -F
   is
   begin
      pragma Assert (F = 0.0);  --  should be true, despite signed zeros
   end Negation_1;

   procedure Identity_1 (F : in out Float)
     with Post => F = F'Old  -- false if F = NaN / +oo
   is
   begin
      F := F - 0.0;
   end Identity_1;

   procedure Identity_2 (X : Float)
     with Pre => X /= 0.0
   is
   begin
      pragma Assert (X / X = 1.0);  -- true in spark, not true in general
   end Identity_2;


   ----------------------------------------------------------------------
   --  Tests for showing off
   ----------------------------------------------------------------------

   procedure Interesting_Inverse_1 (X : Float;
                                    A, B, C : out Float)
   is
   begin
      A := 1.0 / X;
      B := 1.0 / A;
      C := 1.0 / B;
      pragma Assert (A = C);  --  should be true for floats
   end Interesting_Inverse_1;

   procedure Interesting_Inverse_2 (X : Float;
                                    A, B, C : out Float)
   is
   begin
      A := 1.0 / X;
      B := 1.0 / A;
      C := 1.0 / B;
      pragma Assert (X = B);  --  should be false for floats
   end Interesting_Inverse_2;

   ----------------------------------------------------------------------
   --  These tests do nothign too fancy, but they try to go through
   --  most code-paths in VCG to make sure the implementation
   --  is reasonably robust and complete.
   ----------------------------------------------------------------------

   procedure Unary_Ops (X : Float)
   is
   begin
      pragma Assert (- (- X) = + X);
   end Unary_Ops;

   procedure Floats_And_Double (X : Float; Y : Long_Float)
   is
   begin
      pragma Assert ((Float (Y) = X) = (Long_Float (X) = Y));
   end Floats_And_Double;

   procedure Test_Min (X, Y : Float;
                       M    : out Float)
     with Post => M <= X and M <= Y and (M = X or M = Y)
   is
   begin
      M := Float'Min (X, Y);
   end Test_Min;

   procedure Test_Max (X, Y : Float;
                       M    : out Float)
     with Post => M >= X and M >= Y and (M = X or M = Y)
   is
   begin
      M := Float'Max (X, Y);
   end Test_Max;

   procedure Test_Floor_1 (X : Float;
                           Y : out Float)
     with Pre => X >= 0.0,
          Post => Y <= X
   is
   begin
      Y := Float'Floor (X);
   end Test_Floor_1;

   procedure Test_Floor_2 (X : Float)
     with Pre => X >= 0.0
   is
   begin
      pragma Assert (Float'Floor (X) <= Float'Floor (X + 1.0));
   end Test_Floor_2;

   procedure Test_Floor_3 (X : Float)
     with Pre => X in 0.0 .. 16777215.0
   is
   begin
      pragma Assert (X < Float'Floor (X + 1.0));  -- should be true
   end Test_Floor_3;

   procedure Test_Floor_4 (X : Float)
     with Pre => X in 0.0 .. 16777216.0
   is
   begin
      pragma Assert (X < Float'Floor (X + 1.0));  -- should be false
   end Test_Floor_4;

   procedure Test_Floor_5 (X : Float)
   is
   begin
      pragma Assert (Float'Floor (X) <= Float'Ceiling (X));
   end Test_Floor_5;

   procedure Test_Floor_6 (X : Float)
   is
   begin
      --  All these should be true.

      if X = 0.4 then
         pragma Assert (Float'Floor (X)   = 0.0);
         pragma Assert (Float'Ceiling (X) = 1.0);

      elsif X = 0.5 then
         pragma Assert (Float'Floor (X)   = 0.0);
         pragma Assert (Float'Ceiling (X) = 1.0);

      elsif X = 0.6 then
         pragma Assert (Float'Floor (X)   = 0.0);
         pragma Assert (Float'Ceiling (X) = 1.0);

      elsif X = 12.0 then
         pragma Assert (Float'Floor (X)   = 12.0);
         pragma Assert (Float'Ceiling (X) = 12.0);

      elsif X = -0.5 then
         pragma Assert (Float'Floor (X)   = -1.0);
         pragma Assert (Float'Ceiling (X) =  0.0);
      end if;
   end Test_Floor_6;

   procedure Test_Round_1 (X : Float;
                           I : out Integer)
     with Pre => X in -4096.0 .. 4096.0,
     Contract_Cases => (X = -1.6 => I = -2,
                        X = -1.5 => I = -2,
                        X = -1.4 => I = -1,
                        X = -1.0 => I = -1,
                        X =  0.0 => I =  0,
                        X =  1.0 => I =  1,
                        X =  1.4 => I =  1,
                        X =  1.5 => I =  2,
                        X =  1.6 => I =  2)
   is
   begin
      I := Integer (X);
   end Test_Round_1;

   ----------------------------------------------------------------------
   --  Other ideas
   ----------------------------------------------------------------------

   --  a * a = b  =/=>  sqrt(b) = a

   --  n is integral float
   --  1/n + ((n-1)/n)  ==  1  (true in float, false in real,
   --                           false in "obvious" round)

   --  nextup(0) / nextdown(2) = nextup(0)

   --  nextup(0) =? nextup(-0)  -- again, I hate you martin

   --  4096 ** 2 + 1 = 4096 ** 2

   --  x / 2 != x * 0.5

end Foo;

