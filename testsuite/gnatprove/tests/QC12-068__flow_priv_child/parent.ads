package Parent
  --  with Abstract_State => null
  with Abstract_State => State, Initializes => State

  --  Swap comment to switch between a null state and a state with a null
  --  refinement (non-null Abstract_State here requires Refined_State in body).
is
   procedure Foo with Global => null;
end Parent;
