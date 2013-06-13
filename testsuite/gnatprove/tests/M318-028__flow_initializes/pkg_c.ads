package Pkg_C
is
   pragma SPARK_Mode (On);

   State : Integer;

   procedure Do_Stuff
     with Global => (In_Out => State);

   procedure Init
     with Global => (Output => State);

end Pkg_C;
