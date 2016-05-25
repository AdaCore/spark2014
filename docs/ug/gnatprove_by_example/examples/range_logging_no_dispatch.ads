with Logging_No_Dispatch; use type Logging_No_Dispatch.Log_Count;

package Range_Logging_No_Dispatch with
  SPARK_Mode
is
   type Log_Type is new Logging_No_Dispatch.Log_Type with private;

   not overriding
   function Log_Min (Log : Log_Type) return Integer;

   not overriding
   function Log_Max (Log : Log_Type) return Integer;

   overriding
   procedure Init_Log (Log : out Log_Type) with
     Post => Log.Log_Size = 0 and
             Log.Log_Min = Integer'Last and
             Log.Log_Max = Integer'First;

   overriding
   procedure Append_To_Log (Log : in out Log_Type; Incr : in Integer) with
     Pre  => Log.Log_Size < Logging_No_Dispatch.Max_Count,
     Post => Log.Log_Size = Log.Log_Size'Old + 1 and
             Log.Log_Min = Integer'Min (Log.Log_Min'Old, Incr) and
             Log.Log_Max = Integer'Max (Log.Log_Max'Old, Incr);

private

   type Log_Type is new Logging_No_Dispatch.Log_Type with record
     Min_Entry : Integer;
     Max_Entry : Integer;
   end record;

   function Log_Min (Log : Log_Type) return Integer is (Log.Min_Entry);
   function Log_Max (Log : Log_Type) return Integer is (Log.Max_Entry);

end Range_Logging_No_Dispatch;
