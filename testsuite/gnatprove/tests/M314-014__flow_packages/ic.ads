package IC
  with Abstract_State => (State_A, State_B),
       Initializes    => State_A
is
   pragma Elaborate_Body (IC);
end IC;
