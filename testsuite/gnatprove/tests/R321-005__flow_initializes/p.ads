package P with Abstract_State => (State1, State2, State3),
               Initializes => null
is
   procedure Dummy with Global => (Output => (State1, State2));
end;
