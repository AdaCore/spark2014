with Pkg_A;

package Pkg_E
  with Initializes => (State => Pkg_A.State)  --  Pkg_A.State not initialized
  --  this will be detected once we analyse packages
is


   State : Integer;

   procedure Do_Stuff
     with Global   => (In_Out => State),
          Annotate => (GNATprove, Always_Return);

   procedure Init
     with Global   => (Output => State),
          Annotate => (GNATprove, Always_Return);

end Pkg_E;
