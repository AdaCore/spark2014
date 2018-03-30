package body Fraction_Fixed is

   procedure Test_Minus (X : T) is
      Y : constant T := 5.0;
      Z : T;
   begin
      Z := -X;
      pragma Assert (if X > 0.0 then Z < 0.0 elsif X < 0.0 then Z > 0.0 else Z = X);
      Z := -Y;
      pragma Assert (Z <= X);
   end Test_Minus;

   procedure Test_Add (X : T) is
      Y : constant T := 5.0;
      Z : T;
   begin
      Z := X + X;
      pragma Assert (if X > 0.0 then Z > X elsif X < 0.0 then Z < X else Z = X);
      Z := X + Y;
      pragma Assert (Z > X);
      Z := 2.0 + Y;
      pragma Assert (Z = 7.0);
   end Test_Add;

   procedure Test_Subtract (X : T) is
      Y : constant T := 5.0;
      YY : constant Integer := 5;
      Z : T;
   begin
      Z := X - X;
      pragma Assert (Z = 0.0);
      Z := X - Y;
      pragma Assert (Z < X);
      Z := 2.0 - Y;
      pragma Assert (Z = -3.0);
   end Test_Subtract;

   procedure Test_Multiply (X : T) is
      Y : constant T := 2.0;
      Two : Integer := 2;
      Z : T;
      Z2 : T2;
   begin
      Z := X * 2;
      pragma Assert (Z = X + X);
      Z := 2 * X;
      pragma Assert (Z = X + X);
      Z := X * Two;
      pragma Assert (Z = X + X);
      Z := Two * X;
      pragma Assert (Z = X + X);
      --  Z := X * 2.0;
      --  pragma Assert (Z = X + X);
      Z2 := X * Y;
      pragma Assert (Z = X + X);
   end Test_Multiply;

   procedure Test_Divide (X : T) is
      Y : constant T := 0.5;
      Inv_Y : constant T := 2.0;
      Two : Integer := 2;
      Z : T;
      Zint : Tint;
   begin
      if X /= 0.0 then
         Zint := X / X;
         pragma Assert (Zint = 1.0);
      end if;
      Zint := X / T'(Y * 5 + Inv_Y);
      Z := X / 2;
      pragma Assert (X in 2 * Z - T'Small .. 2 * Z + T'Small);
      Z := X / Two;
      pragma Assert (X in 2 * Z - T'Small .. 2 * Z + T'Small);
      --  Z := Y / 2.0;
      --  pragma Assert (Z = 0.25);
   end Test_Divide;

   procedure Test_Compare (X : T) is
   begin
      if X >= 0.0 then
         pragma Assert (not (X < 0.0));
         pragma Assert (2 * X >= X);
         pragma Assert (X + X >= X);
      else
         pragma Assert (X < 0.0);
         pragma Assert (2 * X < X);
         pragma Assert (X + X < X);
      end if;
   end Test_Compare;

end Fraction_Fixed;
