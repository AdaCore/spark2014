with P;

procedure Main is
   D1 : constant Boolean := P.P1.D with Ghost;
   D2 : constant Boolean := P.P2.D with Ghost;
begin
   pragma Assert (D1 /= D2);
end;
