with Logging; use Logging;

procedure Use_Logging_Classwide (Log : out Log_Type'Class) with
  SPARK_Mode
is
begin
   Log_Type (Log).Init_Log;
   Log.Append_To_Log (2);
end Use_Logging_Classwide;
