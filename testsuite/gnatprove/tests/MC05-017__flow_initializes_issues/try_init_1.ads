with P; pragma Elaborate_All (P);

package Try_Init_1
with Initializes => (C => P.V)
is
   C : constant Integer := P.V;
end Try_Init_1;
