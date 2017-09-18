with P1; pragma Elaborate_All (P1);
package body P2 is
   procedure P is null;
begin
   P1.P;
end;
