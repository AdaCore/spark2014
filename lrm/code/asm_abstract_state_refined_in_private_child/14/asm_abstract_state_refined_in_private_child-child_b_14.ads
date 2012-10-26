private package Power.Source_B
with
   Abstract_State => State;
is
   procedure Read (Level : out Integer);
   with
      Global => State,
      Depends => (Level => State);
end Power.Source_B;
