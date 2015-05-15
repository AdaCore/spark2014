with Ada.Text_IO;

package body Debug_IO is

   procedure Put (X : String) renames Ada.Text_IO.Put;

   procedure Put_Line (X : String) renames Ada.Text_IO.Put_Line;

   procedure New_Line is
   begin
      Ada.Text_IO.New_Line (Spacing => 1);
   end New_Line;

end Debug_IO;
