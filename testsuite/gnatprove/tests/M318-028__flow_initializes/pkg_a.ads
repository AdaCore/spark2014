package Pkg_A
  with Abstract_State => State
is


   procedure Do_Stuff
     with Global   => (In_Out => State),
          Always_Terminates;

   procedure Init
     with Global   => (Output => State),
          Always_Terminates;

end Pkg_A;
