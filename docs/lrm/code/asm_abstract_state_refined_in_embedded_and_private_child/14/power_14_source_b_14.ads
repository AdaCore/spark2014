private package Power_14.Source_B_14
   with Abstract_State => State
is
   procedure Read (Level : out Integer)
      with Global  => State,
           Depends => (Level => State);
end Power_14.Source_B_14;
