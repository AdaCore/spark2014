package body Binary_Fixed is
   
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
      Z : T;
   begin
      Z := X * 2;
      pragma Assert (Z = X + X);
      Z := 2 * X;
      pragma Assert (Z = X + X);
      Z := X * 2.0;
      pragma Assert (Z = X + X);
      Z := X * Y;
      pragma Assert (Z = X + X);
   end Test_Multiply;
   
   procedure Test_Divide (X : T) is
      Y : constant T := 0.5;
      Z : T;
   begin
      if X /= 0.0 then
         Z := X / X;
         pragma Assert (Z = 1.0);
      end if;
      Z := X / Y;
      pragma Assert (Z = 2 * X);
      Z := X / 2;
      pragma Assert (X in 2 * Z - T'Small .. 2 * Z + T'Small);
      Z := Y / 2.0;
      pragma Assert (Z = 0.25);
   end Test_Divide;
      
end Binary_Fixed;
   
   
  
