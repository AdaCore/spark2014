with External_Interface;
pragma Elaborate_All (External_Interface);
package body Data_Package with SPARK_Mode is
begin
   declare
      Data : Data_Record;
   begin
      Read_Data_From_File ("data_file_name", Data);
      Data_1 := Data.Field_1;
      Data_2 := Data.Field_2;
      Data_3 := Data.Field_3;
   end;
end Data_Package;
