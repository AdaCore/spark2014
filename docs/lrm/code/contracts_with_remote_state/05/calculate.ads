with Processing;
--# inherit Processing, Raw_Data;
package Calculate
is

   procedure Read_Calculated_Value (Value : out Integer);
   --# global in out Processing.State;
   --#        in     Raw_Data.State;
   --# derives Value, Processing.State from Processing.State, Raw_Data.State;
   --# pre Raw_Data.Data_Is_Valid (Raw_Data.State);

end Calculate;
