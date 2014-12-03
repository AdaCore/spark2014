with Logging; use Logging;
with Use_Logging;

procedure Use_Logging_Classwide (Log : out Log_Type'Class) with
  SPARK_Mode
is
begin
   Use_Logging (Log_Type (Log));
end Use_Logging_Classwide;
