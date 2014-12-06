package Logging_Discr with
  SPARK_Mode
is
   type Log_Kind is (Min_Max_Values, Last_Values);
   type Integer_Array is array (Positive range <>) of Integer;

   type Log_Type (Kind : Log_Kind; Capacity : Natural) is record
      case Kind is
         when Min_Max_Values =>
            Min_Entry : Integer;
            Max_Entry : Integer;
         when Last_Values =>
            Log_Data : Integer_Array (1 .. Capacity);
            Log_Size : Natural;
      end case;
   end record;

   subtype Min_Max_Log is Log_Type (Min_Max_Values, 0);
   subtype Ten_Values_Log is Log_Type (Last_Values, 10);

   function Log_Size (Log : Log_Type) return Natural;

   function Last_Entry (Log : Log_Type) return Integer with
     Pre => Log.Kind = Last_Values and then Log.Log_Size in 1 .. Log.Capacity;

end Logging_Discr;
