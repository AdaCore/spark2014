with Ada.Text_IO;

procedure P is
   pragma SPARK_Mode (Off);
   Input_File_Name : String := "dummy";
begin
   null;
exception
   when others =>
      Ada.Text_IO.Put_Line ("Error in processing " & Input_File_Name);
end P;

