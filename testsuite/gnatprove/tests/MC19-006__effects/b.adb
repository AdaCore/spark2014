with A;

procedure Main is
   Tmp : constant Integer := A.A;
begin
   A.P;
   pragma Assert (Tmp = A.A);
end Main;
