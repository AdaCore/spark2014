with External_Interface; use External_Interface;
package Data_Package with SPARK_Mode,
Initializes => (Data_1 => File_System, Data_2 => File_System, Data_3 => File_System)
is
   pragma Elaborate_Body;
   Data_1 : Data_Type_1;
   Data_2 : Data_Type_2;
   Data_3 : Data_Type_3;
end Data_Package;
