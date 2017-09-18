with P; pragma Elaborate_All (P);

package Try_Init_3
with Abstract_State => (X, Y),
     Initializes => (Y => P.V),
     Elaborate_Body
is
   C : constant Integer := P.V;
end Try_Init_3;
