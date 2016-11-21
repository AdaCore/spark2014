package Dp
with SPARK_Mode,
  Abstract_State => (T)
is

   function Get_X return Integer
     with Global => (Input => T);

   procedure Set_Y (Y : in Integer)
     with Global => (In_Out => T);

end Dp;
