function Sqrt (X : in Float; Tolerance : in Float) return Float is
   Approx : Float;  -- An approximation of the square root of X
begin
   Approx := X / 2.0;
   while abs (X - Approx ** 2) > Tolerance loop
      Approx := 0.5 * (Approx + X / Approx);
   end loop;
   return Approx;
end Sqrt;
