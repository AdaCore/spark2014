with P2;
package body P1 is
  procedure P is null;
begin
  pragma Assert (P2.Body2_Elaborated);
end;
