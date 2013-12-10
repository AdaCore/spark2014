package Pack
   with Abstract_State => State,
        Initializes => State,
        Initial_Condition => Is_Valid
is

   function Is_Valid return Boolean
      with Global => State;

   procedure P
      with Global => State,
           Pre => Is_Valid;
end Pack;
