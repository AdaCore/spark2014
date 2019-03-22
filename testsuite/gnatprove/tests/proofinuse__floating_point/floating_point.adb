with Ada.Unchecked_Conversion;
with Ada.Numerics.Elementary_Functions;

package body Floating_Point with SPARK_Mode
is
   --  CBMC can trivially show this is true
   procedure Range_Add (X : Float_32; Res : out Float_32) is
   begin
      pragma Assume (X in 10.0 .. 1000.0);
      Res := X + 2.0;
      pragma Assert (Res >= 12.0);
   end Range_Add;

   --  CBMC can trivially show this is true
   procedure Range_Mult (X : Float_32; Res : out Float_32) is
   begin
      pragma Assume (X in 5.0 .. 10.0);
      Res := X * 2.0 - 5.0;
      pragma Assert (Res >= X);
   end Range_Mult;

   --  CBMC can show this is true, but it takes a while (25 seconds)
   procedure Range_Add_Mult (X, Y, Z : Float_32; Res : out Float_32) is
   begin
      pragma Assume (X >= 0.0 and then X <= 180.0);
      pragma Assume (Y >= -180.0 and then Y <= 0.0);
      pragma Assume (Z >= 0.0 and then Z <= 1.0);
      pragma Assume (X + Y >= 0.0);
      Res := X + Y * Z;
      pragma Assert (Res >= 0.0 and then Res <= 360.0);
   end Range_Add_Mult;

   --  NOT TRUE. Counterexample posted to N131-061.
   procedure Guarded_Div (X, Y : Float_32; Res : out Float_32) is
      Threshold : constant Float_32 := 1000.0;
   begin
      pragma Assume (X >= 0.0);
      pragma Assume (Y > 0.1);
      pragma Assume (Y < 1.0);
      pragma Assume (X / Threshold <= Y);
      Res := X / Y;
      pragma Assert (Res <= Threshold);  --@ASSERT:FAIL
   end Guarded_Div;

   procedure Guarded_Div_Original (X, Y : Float_32; Res : out Float_32) is
      Threshold : constant Float_32 := 1000.0;
   begin
      pragma Assume (X >= 0.0);
      pragma Assume (Y > 0.0);
      pragma Assume (Y < 1.0);
      pragma Assume (X / Float_32'Last <= Y);
      Res := X / Y;  --@OVERFLOW_CHECK:FAIL
   end Guarded_Div_Original;

   procedure Guarded_Div_Original_Fixed (X, Y : Float_32; Res : out Float_32) is
      Threshold : constant Float_32 := 1000.0;
   begin
      pragma Assume (X >= 0.0);
      pragma Assume (Y > 0.1);
      pragma Assume (Y < 1.0);
      pragma Assume (X / Float_32'Last <= Y);
      Res := X / Y;
   end Guarded_Div_Original_Fixed;

   --  NOT TRUE. Counterexample posted to N131-061.
   procedure Fibonacci (N : Positive; X, Y : Float_32; Res : out Float_32) is
   begin
      pragma Assume (N in 2 .. 46);
      pragma Assume (X < (1.6181**(N-2))/2.2360 + 1.0);
      pragma Assume (Y < (1.6181**(N-1))/2.2360 + 1.0);
      Res := X + Y;
      pragma Assert (Res < (1.6181**N)/2.2360 + 1.0);  --@ASSERT:FAIL
   end Fibonacci;

   --  CBMC can trivially show this is true
   --  I have used 3.27680E+03f as a constant for s_scale
   procedure Int_To_Float_Complex (X   : Unsigned_16;
                                   Y   : Float_32;
                                   Res : out Float_32) is
      S_Max   : constant := 10.0;
      S_MSB   : constant := S_Max * 2.0;
      S_Scale : constant := 2.0 ** 16 / S_MSB;
   begin
      pragma Assume (Y in 0.25 .. 1.0);
      Res := Float_32 (X) / S_Scale;
      if Res >= S_Max then
         Res := Res - S_MSB;
      end if;
      Res := Res / Y;  --  overflow check unprovable
   end Int_To_Float_Complex;

   --  CBMC can trivially show this is true
   procedure Int_To_Float_Simple (X : Unsigned_16; Res : out Float_32) is
      L : constant := 7.3526e6;
   begin
      pragma Assume (X /= 0);
      pragma Assert (Float_32 (X) >= 0.9);  --  @ASSERT:PASS
      Res := L / Float_32 (X);              --  @OVERFLOW_CHECK:PASS
   end Int_To_Float_Simple;

   --  CBMC can trivially show this is true
   function Float_To_Long_Float (X : Float) return Long_Float is
      Tmp : Long_Float;
   begin
      pragma Assume (X >= Float'First and X <= Float'Last);
      Tmp := Long_Float (X);
      pragma Assert
           (Tmp >= Long_Float (Float'First) and
            Tmp <= Long_Float (Float'Last));
      return Tmp;
   end Float_To_Long_Float;

   --  CBMC can show this is true, but it takes a while (7 seconds)
   procedure Incr_By_Const (State : in out Float_32;
                            X     : T)
   is
   begin
      pragma Assume (X < T'Last and State in 0.0 | C .. Float_32 (X) * C);
      State := State + C;
      pragma Assert (State in C .. Float_32 (X + 1) * C);
   end Incr_By_Const;

   --  I have manually verified this; there should be no RTE and the
   --  postcondition will hold. A hand-coded smtlib instance takes around
   --  30 minutes on a modern solver. (Florian)
   function Approximate_Inverse_Square_Root (X : Float) return Float
   is
      function To_Float is new Ada.Unchecked_Conversion (Source => Integer,
                                                         Target => Float);
      function To_Int is new Ada.Unchecked_Conversion (Source => Float,
                                                       Target => Integer);
      I          : Integer;
      Y          : Float;
      X2         : constant Float := X * 0.5;
      Threehalfs : constant Float := 1.5;
   begin
      pragma Assume (X >= 0.00001);
      I := To_Int (X);
      I := 16#5F3759DF# - (I / 2);
      Y := To_Float (I);
      Y := Y * (Threehalfs - (X2 * (Y * Y)));
      --  Y := Y * (Threehalfs - (X2 * (Y * Y)));
      --  Second iteration can be enabled for more precision.
      pragma Assert ((Y * Y) * X in 1.0 - 0.005 .. 1.0 + 0.005);
      return Y;
   end Approximate_Inverse_Square_Root;

   procedure Angle_Between (A_X, A_Y : Coord;
                            B_X, B_Y : Coord;
                            C_X, C_Y : Coord;
                            Res      : out Float)
   is
      Vec_BA_X : constant Float := A_X - B_X;
      Vec_BA_Y : constant Float := A_Y - B_Y;
      Vec_BC_X : constant Float := C_X - B_X;
      Vec_BC_Y : constant Float := C_Y - B_Y;

      BA_Dot_BC : constant Float := Vec_BA_X * Vec_BC_X +
                                    Vec_BA_Y * Vec_BC_Y;

      Length_BA : constant Float := Ada.Numerics.Elementary_Functions.Sqrt
        ((B_X - A_X) ** 2 + (B_Y - A_Y) ** 2);

      Length_BC : constant Float := Ada.Numerics.Elementary_Functions.Sqrt
        ((B_X - C_X) ** 2 + (B_Y - C_Y) ** 2);
   begin
      pragma Assume (Length_BA > 0.001);
      pragma Assume (Length_BC > 0.001);
      Res := BA_Dot_BC / (Length_BA * Length_BC);
      pragma Assert (Res in -1.00001 .. 1.00001);  -- true
      pragma Assert (Res in -1.0 .. 1.0);          -- probably not
   end Angle_Between;

   procedure User_Rule_2 (X, Y, Z : Float;
                          Res     : out Boolean)
   is
   begin
      pragma Assume (X >= 0.0);
      pragma Assume (Y >= 0.0);
      pragma Assume (Z >= 0.0);
      pragma Assume (X <= 16777216.0);
      pragma Assume (Y <= 16777216.0);
      Res := - (X * Y) <= Z;
      pragma Assert (Res);     -- valid
   end User_Rule_2;

   procedure User_Rule_3 (X, Y : Float;
                          Res  : out Boolean)
   is
   begin
      pragma Assume (X < Y);
      pragma Assume (Y > 0.0);
      Res := X / Y <= 1.0;
      pragma Assert (Res);     -- valid
   end User_Rule_3;

   procedure User_Rule_4 (X, Y : Float;
                          Res  : out Boolean)
   is
   begin
      pragma Assume (X <= Y);
      pragma Assume (Y > 0.0);
      Res := X / Y <= 1.0;
      pragma Assert (Res);     -- valid
   end User_Rule_4;

   procedure User_Rule_5 (X   : Float;
                          Res : out Boolean)
   is
   begin
      pragma Assume (X in 0.0 .. 1.0);
      Res := Sqrt (X) <= 1.0;
      pragma Assert (Res);     -- valid
   end User_Rule_5;

   procedure User_Rule_6 (X, Y, Z, A : Float;
                          Res        : out Boolean)
   is
   begin
      pragma Assume (Z >= 0.0);
      pragma Assume (X >= Y);
      pragma Assume (Y >= Z);
      pragma Assume (X > Z);
      pragma Assume (A <= 0.0);
      Res := (X - Y) / (X - Z) >= A;
      pragma Assert (Res);     -- valid
   end User_Rule_6;

   --  User_Rule_7 (although very similar to 6) is surprisingly difficult
   --  to verify.

   procedure User_Rule_7 (X, Y, Z, A : Float;
                          Res        : out Boolean)
   is
   begin
      pragma Assume (Z >= 0.0);
      pragma Assume (X >= Y);
      pragma Assume (Y >= Z);
      pragma Assume (X > Z);
      pragma Assume (A >= 1.0);
      Res := (X - Y) / (X - Z) <= A;
      pragma Assert (Res);     -- valid
   end User_Rule_7;

   procedure User_Rule_8 (A, B, C : Float;
                          Res     : out Boolean)
   is
   begin
      pragma Assume (abs A * abs C < 5800.0 * abs B);
      Res := not (B = 0.0);
      pragma Assert (Res);     -- valid
   end User_Rule_8;

   procedure User_Rule_9 (A, B : Float;
                          Res  : out Boolean)
   is
   begin
      pragma Assume (abs A < 5800.0 * abs B);
      Res := A / B <= 5800.0;
      pragma Assert (Res);     -- valid
   end User_Rule_9;

   procedure User_Rule_10 (A, B : Float;
                           Res  : out Boolean)
   is
   begin
      pragma Assume (abs A < 5800.0 * abs B);
      Res := A / B >= -5800.0;
      pragma Assert (Res);     -- valid
   end User_Rule_10;

   --  The counterexample to 11 involves infinity (a = 0, c = Float'Last)

   procedure User_Rule_11 (A, B, C, D : Float;
                           Res        : out Boolean)
   is
   begin
      pragma Assume (A >= 0.0);
      pragma Assume (B >= 0.0);
      Res := (C * C) * A + (D * D) * B >= 0.0; --@OVERFLOW_CHECK:FAIL
      pragma Assert (Res);
   end User_Rule_11;

   procedure User_Rule_12 (A, B, C, D : Float;
                           Res        : out Boolean)
   is
   begin
      pragma Assume (A >= 0.0);
      pragma Assume (B >= 0.0);
      --  ensures C*C and D*D is finite
      pragma Assume (C in Squarable_Float);
      pragma Assume (D in Squarable_Float);
      Res := (C * C) * A + (D * D) * B >= 0.0;
      pragma Assert (Res);     -- valid
   end User_Rule_12;

   procedure User_Rule_13 (D0, D1, R : Float;
                           Res       : out Boolean)
   is
   begin
      pragma Assume (D1 > D0);
      pragma Assume (R in 0.0 .. 1.0);
      pragma Assume (D0 >= 0.0);
      Res := D1 - ((D1 - D0) * R) >= 0.0;
      pragma Assert (Res);     -- valid
   end User_Rule_13;

   procedure User_Rule_14 (D0, D1, R, X : Float;
                           Res          : out Boolean)
   is
   begin
      pragma Assume (D1 > D0);
      pragma Assume (R in 0.0 .. 1.0);
      pragma Assume (D0 >= 0.0);
      pragma Assume (D1 <= X);
      Res := D1 - ((D1 - D0) * R) <= X;
      pragma Assert (Res);     -- valid
   end User_Rule_14;

   procedure User_Rule_15 (X, Y : Float;
                           Res  : out Boolean)
   is
   begin
      pragma Assume (X in -7800.0 .. 7800.0);
      pragma Assume (Y in -7800.0 .. 7800.0);
      pragma Assume (X > abs Y);
      Res := X * X - Y * Y >= 0.0;
      pragma Assert (Res);     -- valid
   end User_Rule_15;

   procedure User_Rule_16 (X, Y : Float;
                           Res  : out Boolean)
   is
   begin
      pragma Assume (X in -7800.0 .. 7800.0);
      pragma Assume (Y in -7800.0 .. 7800.0);
      pragma Assume (X > abs Y);
      Res := Sqrt (X * X - Y * Y) <= X;
      pragma Assert (Res);     --@ASSERT:FAIL
   end User_Rule_16;

   --  user_rule_17 omitted until I have worked out how to deal with
   --  subnormals in ada

   --  In this simple calculation, it can be easily seen by interval reasoning
   --  that there is no overflow. But current SMT solvers with our encoding
   --  can't solve this.

   procedure Polynomial (X : Float)
   is
   begin
      pragma Assume (X in 0.0 .. 60.0);
      pragma Assert ((((X + 2.0) * X + 3.0) + 4.0) * X + 5.0 in Float'Range);
   end Polynomial;

   procedure Float_Different (X, Y : Float_32; Res : out Float_32) is
   begin
      pragma Assume (X /= Y);
      Res := X - Y;
      pragma Assert (Res /= 0.0);
   end Float_Different;

   procedure Float_Greater (X, Y : Float_32; Res : out Float_32) is
   begin
      pragma Assume (X > Y);
      Res := X - Y;
      pragma Assert (Res > 0.0);
   end Float_Greater;

   procedure Diffs (X, Y, Z : Float) is
   begin
      pragma Assume (X - Y > 0.0);
      pragma Assume (Y - Z > 0.0);
      pragma Assert (X - Z > 0.0);
   end Diffs;

   procedure Sub_Then_Add1 (X, Y : Float_32; Res : out Float_32) is
   begin
      pragma Assume (X >= 0.0);
      pragma Assume (Y >= 0.0);
      pragma Assume (X <= Y);
      Res := X + (Y - X);
      pragma Assert (Res >= X);
      pragma Assert (Res <= Y);  --  @ASSERT:FAIL
   end Sub_Then_Add1;

   procedure Sub_Then_Add2 (X, Y : Float_32; Res : out Float_32) is
   begin
      pragma Assume (X >= 0.0);
      pragma Assume (Y >= 0.0);
      pragma Assume (X >= Y);
      Res := X + (Y - X);
      pragma Assert (Res <= X);
      pragma Assert (Res >= Y);  --  @ASSERT:FAIL
   end Sub_Then_Add2;

   procedure Half_Bound (X : Float_32; Res : out Float_64) is
   begin
      pragma Assume (X in -1.0 .. 1.0);
      Res := Float_64 (X * 0.5);
      pragma Assert (Res in -1.0 .. 1.0);
   end Half_Bound;

end Floating_Point;
