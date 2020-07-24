package Logging_Out with
  SPARK_Mode
is
   Total   : Integer;
   Log_Out : Integer with Volatile, Async_Readers, Effective_Writes;

   procedure Add_To_Total (Incr : in Integer) with
     Global  => (In_Out => Total, Output => Log_Out),
     Depends => (Total =>+ Incr, Log_Out => Incr);

end Logging_Out;
