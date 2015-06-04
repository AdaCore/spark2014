package Other2
  with Abstract_State => (State with External => Async_Writers)
is
   procedure Vol_Proc (X : out Integer)
     with Global => State;
end Other2;
