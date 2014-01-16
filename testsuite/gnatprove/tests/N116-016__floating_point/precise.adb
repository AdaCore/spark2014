procedure Precise is
   X : Float := 10.0;
   Y : Float := 0.4;
   Z : Float;
begin
   Z := X + Y;
   pragma Assert (Z in 10.39999 .. 10.40001);
   Z := X - Y;
   pragma Assert (Z in 9.59999 .. 9.60001);
   Z := X * Y;
   pragma Assert (Z in 3.39999 .. 4.00001);
   Z := X / Y;
   pragma Assert (Z in 24.99999 .. 25.00001);
end Precise;
