with Pkg_B; use Pkg_B;

package body Test is

   procedure Test_01 (N : out Natural)
   is
      Tmp : Widget;
   begin
      New_Widget (Tmp);
      N := Tmp.X;
   end Test_01;

end Test;
