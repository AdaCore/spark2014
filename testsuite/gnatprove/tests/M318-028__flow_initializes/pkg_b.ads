package Pkg_B
  with Abstract_State => State,
       Initializes    => State
is


   procedure Do_Stuff
     with Global   => (In_Out => State),
          Annotate => (GNATprove, Always_Return);

   procedure Init
     with Global   => (Output => State),
          Annotate => (GNATprove, Always_Return);

end Pkg_B;
