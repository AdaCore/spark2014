with Ada.Text_IO;

package body P is
   protected body PT is
      procedure Dummy1 is
         S : constant String := Ada.Text_IO.Get_Line;
      begin
         null;
      end;

      procedure Dummy2 is
         package Nested is
            L : Natural := 0;
         end;

         package body Nested is
         begin
            declare
               S : constant String := Ada.Text_IO.Get_Line;
            begin
               L := S'Length;
            end;
         end;
       begin
          null;
       end;
   end;
end;
