with Pkg_A; use Pkg_A;

package Pkg_B
is

   procedure Case_G_G with Global => (In_Out => State);

   procedure Case_G_NG with Global => (In_Out => State);

   procedure Case_NG_G;

   procedure Case_NG_NG;

end Pkg_b;
