package Initializes_Legal_Helper
  with SPARK_Mode,
       Abstract_State => SH1,
       Initializes    => (SH1, Var_H1)
is
   Var_H1 : Integer;
end Initializes_Legal_Helper;
