with Other;

package Pkg_B
  with Abstract_State => (State_A, State_B, State_C),
       Initializes    => (State_A,
                          State_B => (Other.State_D, Other.X))

is
   pragma Elaborate_Body (Pkg_B);
end Pkg_B;
