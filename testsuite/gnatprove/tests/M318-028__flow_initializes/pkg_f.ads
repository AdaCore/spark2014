with Pkg_B;

package Pkg_F
  with Initializes => (State => Pkg_B.State)  --  OK
is


   State : Integer;

   procedure Do_Stuff
     with Global   => (In_Out => State),
          Annotate => (GNATprove, Always_Return);

   procedure Init
     with Global   => (Output => State),
          Annotate => (GNATprove, Always_Return);

end Pkg_F;
