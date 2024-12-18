pragma Extensions_Allowed (All_Extensions);

with Ada.Text_IO; use Ada.Text_IO;

procedure Example is
   F         : File_Type;
   File_Name : constant String := "simple.txt";
begin
   Create (F, Name => File_Name);
   Put_Line (F, "Hello World #1");
   Put_Line (F, "Hello World #2");
   Put_Line (F, "Hello World #3");
finally
   Put_Line ("Closing file");
   Close (F);
end Example;
