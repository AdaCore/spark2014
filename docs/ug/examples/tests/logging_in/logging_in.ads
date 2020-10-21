package Logging_In with
  SPARK_Mode
is
   Log_In : Integer with Volatile, Async_Writers, Effective_Reads;

   type Integer_Array is array (Positive range 1 .. 100) of Integer;
   Log      : Integer_Array;
   Log_Size : Natural;

   procedure Get with
     Global  => (In_Out => (Log, Log_Size, Log_In)),
     Depends => ((Log_Size, Log_In) =>+ null, Log =>+ (Log_Size, Log_In));

end Logging_In;
