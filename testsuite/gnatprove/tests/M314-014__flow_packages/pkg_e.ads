package Pkg_E
  with Abstract_State => (Meant_To_Be_Init,
                          Meant_To_Be_Unint),
       Initializes => (Vis_A, Vis_B, Meant_To_Be_Init)
is
   pragma Elaborate_Body;

  Vis_A : Integer;
  Vis_B : Integer := 0;
  Vis_C : Integer;
  Vis_D : Integer := 0;

end Pkg_E;
