package P
  with Abstract_State => (State1, State2),
       Initializes    => (State1, State2)
is
private
   package Extra with Abstract_State => (State2e with Part_Of => State2), Initializes => State2e is
      function Get return Integer with Global => State2e;
   end;
   procedure Dummy (Y : out Integer) with Global => State1;
   --                               this should be: (State1, Extra.State2e);
end;
