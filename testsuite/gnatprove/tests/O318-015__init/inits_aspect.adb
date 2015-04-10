package body Inits_Aspect with
  SPARK_Mode,
  Refined_State => (S => X)
is
   X : Integer := 10;
end Inits_Aspect;
