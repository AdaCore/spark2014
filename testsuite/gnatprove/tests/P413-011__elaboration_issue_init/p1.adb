with P2;
package body P1 is
  procedure P is null;
begin
  pragma Assert (P2.Body_Elaborated);
  Body_Elaborated := True;
end;
