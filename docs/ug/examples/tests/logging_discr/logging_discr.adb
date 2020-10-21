package body Logging_Discr with
  SPARK_Mode
is
   function Log_Size (Log : Log_Type) return Natural is
   begin
      case Log.Kind is
         when Min_Max_Values =>
            return 2;
         when Last_Values =>
            return Log.Log_Size;
      end case;
   end Log_Size;

   function Last_Entry (Log : Log_Type) return Integer is
   begin
      return Log.Log_Data (Log.Log_Size);
   end Last_Entry;

end Logging_Discr;
