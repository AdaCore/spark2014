with Ada.Text_IO;

package body pack is

   task body T1 is
   begin
      Ada.Text_IO.Put_Line ("Hi, I am a new task T1!");
   end;

   task body T2 is
   begin
      Ada.Text_IO.Put_Line ("Hi, I am a new task T2!");
   end;

   protected body P is
   end;

end;
