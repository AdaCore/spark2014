package P
  with Abstract_State => State,
       Initializes    => State
is
   function Read_From_State return Integer with Global => State;
end P;
