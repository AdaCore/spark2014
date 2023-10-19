with A;

procedure B is
   Tmp : constant Integer := A.A;
begin
   A.P;
   pragma Assert (Tmp = A.A);
end B;
