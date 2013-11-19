package body Raw_Data
  with SPARK_Mode,
       Refined_State => (State => (Last_Read, In_Port))
is
   pragma Warnings (Off);
   In_Port : Integer := 0
     with Volatile,
          Async_Writers;
   -- Address clause would go here
   pragma Warnings (On);

   Last_Read : Integer := 0;

   function Data_Is_Valid return Boolean
     with Refined_Global => Last_Read
   is
   begin
     return Last_Read /= 0 and Last_Read > -23 and Last_Read < 117;
   end Data_Is_Valid;

   function Get_Value return Integer
     with Refined_Global => Last_Read
   is
   begin
      return Last_Read;
   end Get_Value;

   procedure Read_Next
     with Refined_Global  => (Input  => In_Port,
                              Output=> Last_Read),
          Refined_Depends => (Last_Read => In_Port)
   is
   begin
      Last_Read := In_Port;
      pragma Warnings (Off);
      if not Last_Read'Valid then
      pragma Warnings (On);
         Last_Read := 0;
      end if;
   end Read_Next;
end Raw_Data;
