with Logging_No_Dispatch; use Logging_No_Dispatch;

package Range_Logging_No_Dispatch with
  SPARK_Mode
is
   type Log_Type is private;

   function Log_Size (Log : Log_Type) return Log_Count;

   function Log_Min (Log : Log_Type) return Integer;

   function Log_Max (Log : Log_Type) return Integer;

   procedure Init_Log (Log : out Log_Type) with
     Post => Log_Size (Log) = 0 and
             Log_Min (Log) = Integer'Last and
             Log_Max (Log) = Integer'First;

   procedure Append_To_Log (Log : in out Log_Type; Incr : in Integer) with
     Pre  => Log_Size (Log) < Logging_No_Dispatch.Max_Count,
     Post => Log_Size (Log) = Log_Size (Log)'Old + 1 and
             Log_Min (Log) = Integer'Min (Log_Min (Log)'Old, Incr) and
             Log_Max (Log) = Integer'Max (Log_Max (Log)'Old, Incr);

private

   type Log_Type is tagged record
     Log : Logging_No_Dispatch.Log_Type;
     Min_Entry : Integer;
     Max_Entry : Integer;
   end record;

   function Log_Size (Log : Log_Type) return Log_Count is (Log_Size (Log.Log));

   function Log_Min (Log : Log_Type) return Integer is (Log.Min_Entry);
   function Log_Max (Log : Log_Type) return Integer is (Log.Max_Entry);

end Range_Logging_No_Dispatch;
