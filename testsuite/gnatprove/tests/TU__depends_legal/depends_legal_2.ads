package Depends_Legal_2
  with SPARK_Mode,
       Abstract_State => State,
       Initializes    => State
is
   pragma Elaborate_Body (Depends_Legal_2);
end Depends_Legal_2;
