package body Logging_Priv with
  SPARK_Mode
is
   procedure Append_To_Log (Log : in out Log_Type; Incr : in Integer) is
   begin
      Log.Log_Size := Log.Log_Size + 1;
      Log.Log_Data (Log.Log_Size) := Incr;
   end Append_To_Log;

end Logging_Priv;
