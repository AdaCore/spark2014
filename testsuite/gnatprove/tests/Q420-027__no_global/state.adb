package body State with
  SPARK_Mode => Off,
  Refined_State => (State => S)
is

   function State return State_Type is (S)
     with Refined_Global => S;

   -- procedure Test is null;
end State;
