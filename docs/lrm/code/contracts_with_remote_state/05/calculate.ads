with Processing;
--# inherit Processing, Raw_Data;
package Calculate
is

   procedure Read_Calculated_Value (Value : out Integer);
   --# global in Processing.State, Raw_Data.State;
   --# derives Value from Processing.State, Raw_Data.State;
   --# post Raw_Data.Data_Is_Valid (Value);

end Calculate;
