private package Refined_State_Legal.Priv_Child
  with SPARK_Mode,
       Abstract_State => (Priv_State with Part_Of => S1),
       Initializes    => Priv_State
is
   function F1 return Integer
     with Global => Priv_State;
end Refined_State_Legal.Priv_Child;
