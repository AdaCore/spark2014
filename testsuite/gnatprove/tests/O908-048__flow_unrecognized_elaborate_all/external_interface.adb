with Ada.Text_IO; use Ada.Text_IO;
package body External_Interface with SPARK_Mode => Off is
   procedure Read_Data_From_File (File_Name : String; Data : out Data_Record) is
   begin
      Data := (Data_Type_1'Value (Get_Line (Standard_Input)),
               Data_Type_2'Value (Get_Line (Standard_Input)),
               Data_Type_3'Value (Get_Line (Standard_Input)));
   end Read_Data_From_File;
end External_Interface;
