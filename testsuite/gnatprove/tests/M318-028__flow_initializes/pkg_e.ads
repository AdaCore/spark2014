with Pkg_A;

package Pkg_E
  with Initializes => (State => Pkg_A.State)  --  Pkg_A.State not initialized
  --  this will be detected once we analyse packages
is


   State : Integer;

   procedure Do_Stuff
     with Global => (In_Out => State);

   procedure Init
     with Global => (Output => State);

end Pkg_E;
