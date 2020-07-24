package body Logging_Out_Abstract with
  SPARK_Mode,
  Refined_State => (State => (Log_Out, Total))
is
   Total   : Integer := 0;
   Log_Out : Integer := 0 with Volatile, Async_Readers, Effective_Writes;

   procedure Add_To_Total (Incr : in Integer) with
     Refined_Global  => (In_Out => Total, Output => Log_Out),
     Refined_Depends => (Total =>+ Incr, Log_Out => Incr)
   is
   begin
      Total := Total + Incr;
      Log_Out := Incr;
   end Add_To_Total;

end Logging_Out_Abstract;
