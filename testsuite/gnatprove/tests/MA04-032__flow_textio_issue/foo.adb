with Ada.Text_IO; use Ada.Text_IO;

procedure Foo
  with Global => (In_Out => File_System)
is
   F : File_Type;
begin
   Open (File => F,
         Name => "foo.txt",
         Mode => Out_File);
end Foo;
