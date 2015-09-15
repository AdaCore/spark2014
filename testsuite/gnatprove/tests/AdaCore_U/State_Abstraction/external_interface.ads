package External_Interface
with SPARK_Mode, Abstract_State => File_System, Initializes => File_System is
   type Data_Type_1 is new Integer;
   type Data_Type_2 is new Integer;
   type Data_Type_3 is new Integer;

   type Data_Record is record
      Field_1 : Data_Type_1;
      Field_2 : Data_Type_2;
      Field_3 : Data_Type_3;
   end record;

   procedure Read_Data_From_File (File_Name : String; Data : out Data_Record) with
   Global => File_System;
end External_Interface;
