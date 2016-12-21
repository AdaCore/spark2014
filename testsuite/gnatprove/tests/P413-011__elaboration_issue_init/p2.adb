with P1;
package body P2 is
  procedure P is null;
begin
  pragma Assert (P1.Body_Elaborated);
  Body_Elaborated := True;
end;
