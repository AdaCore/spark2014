
with Ada.Command_Line;    use Ada.Command_Line;
with Ada.Text_IO;         use Ada.Text_IO;

procedure Main is
begin
   begin
      if Argument(1) = "-version" then
         Put_Line ("This is CVC3 version 2.4.1");
         return;
      end if;
   exception
      when others =>
         Put_Line ("Valid.");
         return;
   end;
   Put_Line ("Valid.");
   return;
end Main;
