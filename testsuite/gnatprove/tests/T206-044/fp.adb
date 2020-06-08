procedure Fp is
   type F is delta 0.1 range 0.0 .. 10.0;
   X : F := 0.5;
begin
   X := X * 2.0;
   X := 2.0 * X;
   X := X / 2.0;
end Fp;
