with Logging; use type Logging.Log_Count;

package Range_Logging with
  SPARK_Mode
is
   type Log_Type is new Logging.Log_Type with private;

   not overriding
   function Log_Min (Log : Log_Type) return Integer;

   not overriding
   function Log_Max (Log : Log_Type) return Integer;

   overriding
   procedure Init_Log (Log : out Log_Type) with
     Post'Class => Log.Log_Size = 0 and
                   Log.Log_Min = Integer'Last and
                   Log.Log_Max = Integer'First;

   overriding
   procedure Append_To_Log (Log : in out Log_Type; Incr : in Integer) with
     Pre'Class  => Log.Log_Size < Logging.Max_Count,
     Post'Class => Log.Log_Size = Log.Log_Size'Old + 1 and
                   Log.Log_Min = Integer'Min (Log.Log_Min'Old, Incr) and
                   Log.Log_Max = Integer'Max (Log.Log_Max'Old, Incr);

private

   type Log_Type is new Logging.Log_Type with record
     Min_Entry : Integer;
     Max_Entry : Integer;
   end record;

   function Log_Min (Log : Log_Type) return Integer is (Log.Min_Entry);
   function Log_Max (Log : Log_Type) return Integer is (Log.Max_Entry);

end Range_Logging;
