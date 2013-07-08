package Other
  with Abstract_State => (State_D, State_E),
       Initializes    => (State_D, Y)
is

   pragma Elaborate_Body (Other);

   X : Integer;
   Y : Integer;

end Other;
