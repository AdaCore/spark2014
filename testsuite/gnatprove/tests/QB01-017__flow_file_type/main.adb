with Ada.Text_IO;

procedure Main is
   FD : Ada.Text_IO.File_Type;
begin
   Ada.Text_IO.Open (File => FD,
                     Mode => Ada.Text_IO.Out_File,
                     Name => "dummy.txt");
end;
