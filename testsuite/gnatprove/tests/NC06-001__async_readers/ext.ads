package Ext with
  SPARK_Mode
is
   V1 : Integer with Volatile, Async_Readers;
   V2 : Integer with Volatile, Async_Writers;

   procedure Write with
     Depends => (V1 => null, V2 => null);

end Ext;
