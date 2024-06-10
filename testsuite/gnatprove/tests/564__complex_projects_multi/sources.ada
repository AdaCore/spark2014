package Pkg is
   procedure Execute;
end Pkg;

with Ada.Text_IO; use Ada.Text_IO;
package body Pkg is
   procedure Execute is
   begin
      Put_Line ("Pkg.Execute");
   end Execute;
end Pkg;

with Pkg;
procedure Main is
begin
   Pkg.Execute;
end Main;
