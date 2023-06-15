package Lights
  with Abstract_State => (State with External)
is

   procedure Init
     with Global   => (Output => State),
          Depends  => (State => null),
          Always_Terminates;

   procedure Toggle
     with Global   => (In_Out => State),
          Depends  => (State => State),
          Always_Terminates;

   procedure Explode
     with Global => (Output => State),
          No_Return,
          Exceptional_Cases => (others => False);

end Lights;
