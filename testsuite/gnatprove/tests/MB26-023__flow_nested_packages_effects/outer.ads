with Init; pragma Elaborate_All (Init);

package Outer
  with SPARK_Mode,
       Abstract_State => State,
       Initializes    => (State => Init.Var)
is
   pragma Elaborate_Body (Outer);
end Outer;
