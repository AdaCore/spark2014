procedure Set_Input_File (File : File_Type) with
  SPARK_Mode => Off
is
begin
  Set_Input (File);
end Set_Input_File;
