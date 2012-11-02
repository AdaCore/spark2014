with Raw_Data;
--# inherit Raw_Data;
package Processing
--# own State;
is

   procedure Read_Processed_Data (Value : out Integer);
   --# global in State, Raw_Data.State;
   --# derives Value from State, Raw_Data.State;
   --# post Raw_Data.Data_Is_Valid (Value);

end Processing;
