with Ada.Unchecked_Conversion;

package body Floating_Point with
  SPARK_Mode
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

   --  NOT TRUE. Counter-example posted to N131-061.
   procedure Guarded_Div (X, Y : Float_32; Res : out Float_32) is
      Threshold : constant Float_32 := 1000.0;
   begin
      pragma Assume (X >= 0.0);
      pragma Assume (Y > 0.1);
      pragma Assume (Y < 1.0);
      pragma Assume (X / Threshold <= Y);
      Res := X / Y;
      pragma Assert (Res < Threshold);  --@ASSERT:FAIL
   end Guarded_Div;

   --  NOT TRUE. Counter-example posted to N131-061.
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

end Floating_Point;
