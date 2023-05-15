package Pkg_D
  with Initializes => State
is


   State : Integer;

   procedure Do_Stuff
     with Global   => (In_Out => State),
          Always_Terminates;

   procedure Init
     with Global   => (Output => State),
          Always_Terminates;

end Pkg_D;
