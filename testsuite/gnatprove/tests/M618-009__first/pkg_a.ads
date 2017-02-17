package Pkg_A
  with Initializes => (X, Y),
       Initial_Condition => X = Y
is
   pragma Elaborate_Body (Pkg_A);


   X : Integer := 0;
   Y : Integer;

end Pkg_A;
