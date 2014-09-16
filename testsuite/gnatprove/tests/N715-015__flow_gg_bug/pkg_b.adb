with Pkg_A;

package body Pkg_B with SPARK_Mode => Off
is

   procedure New_Widget (X : out Widget)
   is
   begin
      X := (0, Pkg_A.G);
   end New_Widget;

end Pkg_B;
