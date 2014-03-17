with GNAT.IO;
with Example;

procedure Main is
   Y : Example.Y_T;
begin
   Y := Example.Calculate(15.0);
   GNAT.IO.Put_Line (Example.Y_T'Image(Y));
end Main;
