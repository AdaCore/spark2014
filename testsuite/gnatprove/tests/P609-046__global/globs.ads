package Globs with
  SPARK_Mode,
  Abstract_State => State
is
   function Pub return Integer with Global => State;
   procedure Pub_Out with Global => (Output => State);

end Globs;
