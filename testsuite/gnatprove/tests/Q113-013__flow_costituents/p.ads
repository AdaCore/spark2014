package P
  with Abstract_State => State,
       Initializes => State
is
   pragma Elaborate_Body (P);
end P;
