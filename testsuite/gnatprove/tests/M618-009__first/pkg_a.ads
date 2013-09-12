package Pkg_A
  with Initializes => X
is
   pragma Elaborate_Body (Pkg_A);
   

   X : Integer;
   Y : Integer;

end Pkg_A;
