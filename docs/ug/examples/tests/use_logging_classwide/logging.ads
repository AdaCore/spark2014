package Logging with
  SPARK_Mode
is
   Max_Count : constant := 10_000;

   type Log_Count is range 0 .. Max_Count;

   type Log_Type is tagged private;

   function Log_Size (Log : Log_Type) return Log_Count;

   procedure Init_Log (Log : out Log_Type) with
     Post'Class => Log.Log_Size = 0;

   procedure Append_To_Log (Log : in out Log_Type; Incr : in Integer) with
     Pre'Class  => Log.Log_Size < Max_Count,
     Post'Class => Log.Log_Size = Log.Log_Size'Old + 1;

private

   subtype Log_Index is Log_Count range 1 .. Max_Count;
   type Integer_Array is array (Log_Index) of Integer;

   type Log_Type is tagged record
      Log_Data : Integer_Array;
      Log_Size : Log_Count;
   end record;

   function Log_Size (Log : Log_Type) return Log_Count is (Log.Log_Size);

end Logging;
