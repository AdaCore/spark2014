with My_Data_Protected_By_Lock;
package Use_Data with SPARK_Mode is

   --  Create a package giving a shared access to an integer protected by a lock.
   --  Each thread should use its own instance of the package.
   package Int_Data is new My_Data_Protected_By_Lock (Integer, 42);
   use Int_Data;

   procedure Write_To_Data (I : Integer) with
     Pre  => Get_State_For_Calling_Task = Unknown,
     Post => Get_State_For_Calling_Task = Unknown;
   --  Try to aquire the lock in an active loop and write I inside data

   procedure Bad_Write_To_Data (I : Integer) with
     Pre  => Get_State_For_Calling_Task = Unknown,
     Post => Get_State_For_Calling_Task = Unknown;
   --  Write I inside data without aquiring the lock

end Use_Data;
