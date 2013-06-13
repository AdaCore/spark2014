package Pkg_A
  with Abstract_State => State
is
   pragma SPARK_Mode (On);

   procedure Do_Stuff
     with Global => (In_Out => State);

   procedure Init
     with Global => (Output => State);

end Pkg_A;
