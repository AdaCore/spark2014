with Other;

package Pkg_D
with Initializes => (X => Other.X,
                     Y => Other.Y,
                     Z => null)
is
   pragma Elaborate_Body (Pkg_D);

   X : Integer;
   Y : Integer;
   Z : Integer;
end Pkg_D;
