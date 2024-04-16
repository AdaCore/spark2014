package Pkg2 is
   procedure Execute (X : in out Integer);
end Pkg2;

with Ada.Text_IO; use Ada.Text_IO;
package body Pkg2 is
   procedure Execute (X : in out Integer) is
   begin
      X := X + 1;
      Put_Line ("Pkg.Execute");
   end Execute;
end Pkg2;

with Pkg2;
procedure Main2 (X : in out Integer) is
begin
   X := X + 1;
   Pkg2.Execute (X);
end Main2;
