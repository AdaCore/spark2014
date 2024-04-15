with Ada.Direct_IO;

separate (Pkg)
procedure Sub (X : in out Integer) is
begin
   X := X + 1;
   Put_Line ("from sub");
end Sub;
