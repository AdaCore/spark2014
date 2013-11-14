with Raw_Data;
--# inherit Raw_Data;
package Processing
--# own State;
--# Initializes State;
is

   procedure Get_Processed_Data (Value : out Integer);
   --# global in     Raw_Data.State;
   --#        in out State;
   --# derives Value, State  from State, Raw_Data.State;
   --# pre Raw_Data.Data_Is_Valid (Raw_Data.State);

end Processing;
