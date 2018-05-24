package Q with Abstract_State => (State1, State2)
is
   procedure Initialize
     with Global => (Output => (State1, State2));

private
   B : Integer := 0 with Part_Of => State1;
   C : Integer := 0 with Part_Of => State2;
end Q;
