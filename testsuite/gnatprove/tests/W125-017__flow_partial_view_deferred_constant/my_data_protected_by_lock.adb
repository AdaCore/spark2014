package body My_Data_Protected_By_Lock with SPARK_Mode => Off is

   function Get_RW_Access (M : not null access Data_Holder) return not null access Data_Type is (M.The_Data);

   function Get_R_Access (M : not null access constant Data_Holder) return not null access constant Data_Type is (M.The_Data);

   procedure Lock (Success : out Boolean) is null;
   --  Here do nothing but aquire the lock

   procedure Unlock is null;
   --  Here do nothing but release the lock

   function Get_State_For_Calling_Task return Lock_Status is (Unknown);
   --  Return Locked if the current thread has the lock and Unknown otherwise.
   --  Can be left unimplemented if unexecutable ghost code is fine.

end My_Data_Protected_By_Lock;
