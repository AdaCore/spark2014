package P
  with Abstract_State => State,
       Initializes => State
is
   pragma Elaborate_Body;
   function Read_Secret return Boolean with Global => State;
end;
