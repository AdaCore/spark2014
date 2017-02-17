package Pkg_B
  with Abstract_State => State,
       Initializes    => State
is


   procedure Do_Stuff
     with Global => (In_Out => State);

   procedure Init
     with Global => (Output => State);

end Pkg_B;
