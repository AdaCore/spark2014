with P1;
package body P2 is
  procedure P is null;
begin
  pragma Assert (P1.Body1_Elaborated);
  Body2_Elaborated := True;
end;
