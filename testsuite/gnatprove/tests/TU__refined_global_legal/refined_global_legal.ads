package Refined_Global_Legal
  with SPARK_Mode,
       Abstract_State => (State, State2, State3),
       Initializes    => (State2, State3)
is
   procedure P1
     with Global => (Input  => State,
                     Output => State2,
                     In_Out => State3);
end Refined_Global_Legal;
