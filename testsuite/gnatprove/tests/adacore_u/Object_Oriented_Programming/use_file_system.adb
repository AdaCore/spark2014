with File_System; use File_System;

procedure Use_File_System (F : out File'Class)
  with SPARK_Mode
is
begin
   F.Create;
   F.Open_Read;
   F.Close;

   F.Open_Read_Write;
   F.Close;

   F.Open_Read;
   F.Open_Read_Write;
end Use_File_System;
