with Lib;
procedure Main is
   A : constant Integer := Lib.X;
begin
   Lib.Empty;
   pragma Assert (Lib.X = A);
end Main;
