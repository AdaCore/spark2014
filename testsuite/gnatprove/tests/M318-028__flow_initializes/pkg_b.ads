package Pkg_B
  with Abstract_State => State,
       Initializes    => State
is


   procedure Do_Stuff
     with Global   => (In_Out => State),
          Always_Terminates;

   procedure Init
     with Global   => (Output => State),
          Always_Terminates;

end Pkg_B;
