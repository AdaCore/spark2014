package Inits_Aspect with
  SPARK_Mode,
  Abstract_State => S,
  Initializes => S
is
   pragma Elaborate_Body;

   Y : Integer := 0;
end Inits_Aspect;
