package Pkg_B
  with Abstract_State => State,
       Initializes    => State
is
   pragma SPARK_Mode (On);

   procedure Do_Stuff
     with Global => (In_Out => State);

   procedure Init
     with Global => (Output => State);

end Pkg_B;
