package P
   with Abstract_State => State, Initializes => State
is
   procedure Use_State with Global => (Input => State);
end;
