package Logging_Priv with
  SPARK_Mode
is
   Max_Count : constant := 100;

   type Log_Type is private with
     Default_Initial_Condition => Log_Size (Log_Type) = 0;

   function Log_Size (Log : Log_Type) return Natural;

   procedure Append_To_Log (Log : in out Log_Type; Incr : in Integer) with
     Pre => Log_Size (Log) < Max_Count;

private

   type Integer_Array is array (1 .. Max_Count) of Integer;

   type Log_Type is record
     Log_Data : Integer_Array;
     Log_Size : Natural := 0;
   end record;

   function Log_Size (Log : Log_Type) return Natural is (Log.Log_Size);

end Logging_Priv;
