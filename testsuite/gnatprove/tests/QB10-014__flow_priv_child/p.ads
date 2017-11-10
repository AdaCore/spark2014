package P with Abstract_State => S, Initializes => (S,Z) is
   pragma Elaborate_Body;
   Z : Boolean;
end;
