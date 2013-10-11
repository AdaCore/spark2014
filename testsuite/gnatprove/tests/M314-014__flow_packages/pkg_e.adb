package body Pkg_E
  with Refined_State => (Meant_To_Be_Init => (X, Y),
                         Meant_To_Be_Unint => (Z, W))
is

  X : Integer;
  Y : Integer;
  Z : Integer;
  W : Integer;

begin

   Y := 0;
   W := Y;

end Pkg_E;
