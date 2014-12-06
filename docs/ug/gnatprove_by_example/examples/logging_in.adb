package body Logging_In with
  SPARK_Mode
is
   procedure Get is
   begin
      Log_Size := Log_Size + 1;
      Log (Log_Size) := Log_In;
   end Get;

end Logging_In;
