package Pkg_C with Abstract_State => State
is

   procedure Partial_Init_With_Global
   with Global => (In_Out => State);

   procedure Partial_Init_Without_Global;

   procedure Case_G_G with Global => (In_Out => State);

   procedure Case_G_NG with Global => (In_Out => State);

   procedure Case_NG_G;

   procedure Case_NG_NG;

end Pkg_C;
