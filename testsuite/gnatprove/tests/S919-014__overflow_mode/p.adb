pragma SPARK_Mode;
pragma Overflow_Mode (General => Strict, Assertions => Eliminated);

procedure P (X, Y, Z : Natural) is
   pragma Overflow_Mode (General => Strict, Assertions => Strict);
begin
   pragma Assert (X + X = 2 * X);
   pragma Assert (X * Y = Y * X);
   pragma Assert (X ** Y >= Integer'Min(X, 1));
end P;
