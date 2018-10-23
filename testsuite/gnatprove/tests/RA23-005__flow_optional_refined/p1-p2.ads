private package P1.P2 with
  Abstract_State => (State2 with Part_Of => P1.State1),
  Initializes => State2
is
   function F return Integer with Global => State1;
   --  The global contract is fine, even though it could be more precise,
   --  i.e. "Global => State2".
end;
