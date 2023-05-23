package body Use_Data with SPARK_Mode is

   procedure Write_To_Data (I : Integer) is
      Acquired : Boolean;
   begin
      loop
         pragma Loop_Invariant (Get_State_For_Calling_Task = Unknown);
         Lock (Acquired);
         exit when Acquired;
      end loop;
      declare
         Local_Data : access Integer := Get_RW_Access (Data);
      begin
         Local_Data.all := I;
      end;
      UnLock;
   end Write_To_Data;

   procedure Bad_Write_To_Data (I : Integer) is
      Local_Data : access Integer := Get_RW_Access (Data);
   begin
      Local_Data.all := I;
   end Bad_Write_To_Data;

end Use_Data;
