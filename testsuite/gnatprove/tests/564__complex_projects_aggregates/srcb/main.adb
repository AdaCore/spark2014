with Ada.Text_IO;
with Pkg;

procedure Main is
   X : Integer := 42;
begin
   Pkg (Ada.Text_IO.Put_Line'Access, X);
end Main;
