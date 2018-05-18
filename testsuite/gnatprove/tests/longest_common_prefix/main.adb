with Types; use Types;
with LCP;
with Ada.Text_IO; use Ada.Text_IO;
procedure Main is
   A : constant Text := (1, 2, 3, 4, 5, 1, 2, 3, 4, 5);
begin
   Put_Line ("LCP returns non-null");
   pragma Assert (LCP (A, 1, 6) = 5);
   Put_Line ("LCP returns null");
   pragma Assert (LCP (A, 1, 7) = 0);
end Main;
