with Ada.Text_IO;

package body Aida.Text_IO is
   pragma SPARK_Mode (Off);

   procedure Put_Line (Item : String)
   is
   begin
      Ada.Text_IO.Put_Line(Item);
   end Put_Line;

end Aida.Text_IO;
