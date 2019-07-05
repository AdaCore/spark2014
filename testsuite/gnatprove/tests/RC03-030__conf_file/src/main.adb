
with Ada.Command_Line;    use Ada.Command_Line;
with Ada.Text_IO;         use Ada.Text_IO;

procedure Main is
begin
   begin
      if Argument(1) = "-version" then
         Put_Line ("Z3 version 4.4.0");
         return;
      end if;
   exception
      when others =>
         Put_Line ("unsat");
         return;
   end;
   Put_Line ("unsat");
   return;
end Main;
