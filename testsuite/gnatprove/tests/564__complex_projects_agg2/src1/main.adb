with Pkg;

procedure Main (X : in out Integer) is
begin
   X := X + 1;
   Pkg.Put_Line ("Hello");
end Main;
