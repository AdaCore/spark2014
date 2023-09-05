
with Ada.Text_IO;
with blip;


procedure Main is


begin
   Ada.Text_IO.Put_Line("Hello");
   Ada.Text_IO.Put("4 squared is ");
   Ada.Text_IO.Put(Integer'Image(blip.Square(4)));
      Ada.Text_IO.Put_Line(".");

end Main;
