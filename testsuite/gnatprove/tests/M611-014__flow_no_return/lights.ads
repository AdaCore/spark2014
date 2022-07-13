package Lights
  with Abstract_State => (State with External)
is

   procedure Init
     with Global   => (Output => State),
          Depends  => (State => null),
          Annotate => (GNATprove, Always_Return);

   procedure Toggle
     with Global   => (In_Out => State),
          Depends  => (State => State),
          Annotate => (GNATprove, Always_Return);

   procedure Explode
     with Global => (Output => State),
          No_Return;

end Lights;
