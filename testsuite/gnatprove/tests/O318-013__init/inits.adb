package body Inits with
  SPARK_Mode,
  Refined_State => (S => (X, Y))
is
   X : Integer := 10;
   Y : Float;
end Inits;
