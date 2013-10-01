package Pkg_A
  with Initializes => X,
       Initial_Condition => X = Y
is
   pragma Elaborate_Body (Pkg_A);


   X : Integer;
   Y : Integer;

end Pkg_A;
