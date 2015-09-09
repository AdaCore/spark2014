package Pkg_A with Abstract_State => State
is

   procedure Partial_Init_With_Global
   with Global => (In_Out => State);

   procedure Partial_Init_Without_Global;

end Pkg_A;
