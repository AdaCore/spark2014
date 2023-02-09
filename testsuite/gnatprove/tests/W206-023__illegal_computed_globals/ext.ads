package Ext with SPARK_Mode is

   X : Integer;
   Y : Integer with Volatile, Effective_Reads, Async_Writers;
   Z : Integer with Volatile, Async_Writers;

   function Read_And_Write_X return Integer;
   --  Function with computed global outputs

   function Read_Y return Integer with Volatile_Function;
   --  Volatile function reading a variable with effective reads

   function Read_Z return Integer;
   --  Non volatile function reading a volatile variable
end Ext;
