package Pack
  with Abstract_State => (State1, State2),
       Initializes    => (Var, State1, State2)
is
   Var : Integer := 0;

   procedure Initialize_State
     with Global => (Output => State1),
          Depends => (State1 => null);
end Pack;
