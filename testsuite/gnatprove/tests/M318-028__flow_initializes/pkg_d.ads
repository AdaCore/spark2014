package Pkg_D
  with Initializes => State
is


   State : Integer;

   procedure Do_Stuff
     with Global   => (In_Out => State),
          Annotate => (GNATprove, Always_Return);

   procedure Init
     with Global   => (Output => State),
          Annotate => (GNATprove, Always_Return);

end Pkg_D;
