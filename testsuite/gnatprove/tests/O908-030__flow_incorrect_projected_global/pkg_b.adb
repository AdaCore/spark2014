package body Pkg_B
is

   procedure Case_G_G is
   begin
      Pkg_A.Partial_Init_With_Global;
   end Case_G_G;

   procedure Case_G_NG is
   begin
      Pkg_A.Partial_Init_Without_Global;
   end Case_G_NG;

   procedure Case_NG_G is
   begin
      Pkg_A.Partial_Init_With_Global;
   end Case_NG_G;

   procedure Case_NG_NG is
   begin
      Pkg_A.Partial_Init_Without_Global;
   end Case_NG_NG;

end Pkg_B;
