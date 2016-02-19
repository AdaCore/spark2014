package Initializes_Legal_Helper
with Abstract_State => SH1,
     Initializes    => (SH1, Var_H1),
     Elaborate_Body
is
   Var_H1 : Integer;
end Initializes_Legal_Helper;
