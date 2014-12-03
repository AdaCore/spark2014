with Logging; use Logging;

procedure Use_Logging (Log : out Log_Type) with
  SPARK_Mode
is
begin
   Log.Init_Log;
   Append_To_Log (Log, 1);
end Use_Logging;
