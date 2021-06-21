package body Logging_In_Abstract with
  SPARK_Mode,
  Refined_State => (State => (Log_In, Log, Log_Size))
is
   Log_In : Integer with Volatile, Async_Writers, Effective_Reads;

   type Integer_Array is array (Positive range 1 .. 100) of Integer;
   Log      : Integer_Array := (others => 0);
   Log_Size : Natural := 0;

   procedure Get with
     Refined_Global  => (In_Out => (Log, Log_Size, Log_In)),
     Refined_Depends => ((Log_Size, Log_In) =>+ null, Log =>+ (Log_Size, Log_In))
   is
   begin
      Log_Size := Log_Size + 1;
      Log (Log_Size) := Log_In;
   end Get;

end Logging_In_Abstract;
