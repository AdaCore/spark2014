procedure Pos (X, Y : Float) with
  Pre => X >= 1.0 and X <= 1_000_000.0 and Y >= 1.0 and Y <= 1_000_000.0
is
   Z : Float;
begin
   pragma Assert (X >= 1.0);
   pragma Assert (X <= 1_000_000.0);
   pragma Assert (Y >= 1.0);
   pragma Assert (Y <= 1_000_000.0);

   Z := X + Y;
   pragma Assert (Z >= 0.0);
   Z := X - Y;
   pragma Assert (Z <= X);
   Z := X * Y;
   pragma Assert (Z >= 0.0);
   Z := X / Y;
   pragma Assert (Z >= 0.0);
end Pos;
