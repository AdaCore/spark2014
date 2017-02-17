procedure Nonlinear (X, Y, Z : Float)
  with SPARK_Mode
is
   Result : Float;
begin
   pragma Assume(X >= 0.0 and then X <= 180.0);
   pragma Assume(Y >= -180.0 and then Y <= 0.0);
   pragma Assume(Z >= 0.0 and then Z <= 1.0);
   pragma Assume(X + Y >= 0.0);
   Result := X + Y * Z;
   pragma Assert (Result >= 0.0 and then Result <= 360.0);
end Nonlinear;
