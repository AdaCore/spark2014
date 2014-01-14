package Pack
  with SPARK_Mode,
       Abstract_State => State,
       Initializes    => State
is
   Var : Integer;

   procedure Initialize_State
     with Global => (Output => State);
end Pack;
