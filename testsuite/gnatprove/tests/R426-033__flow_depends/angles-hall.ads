package Angles.Hall with Abstract_State => State is

   procedure Update (Position : out Integer) with
     Global  => (In_Out => (Angles.State, State)),
     Depends => (Angles.State =>+ State,
                 Position     => (Angles.State, State),
                 State        => State);

   -- Same as the one above, but does not give any output
   procedure Update with
     Global => (In_Out => (State, Angles.State)),
     Depends => (Angles.State =>+ State,
                 State        => State);

end Angles.Hall;
