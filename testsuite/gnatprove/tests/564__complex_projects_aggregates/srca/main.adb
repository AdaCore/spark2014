with Ada.Text_IO;
with Pkg;

procedure Main is
   procedure My_Pkg is new Pkg (Ada.Text_IO.Put_Line);
   X : Integer := 42;
begin
   My_Pkg (X);
end Main;
