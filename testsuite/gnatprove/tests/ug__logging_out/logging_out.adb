package body Logging_Out with
  SPARK_Mode
is
   procedure Add_To_Total (Incr : in Integer) is
   begin
      Total := Total + Incr;
      Log_Out := Incr;
   end Add_To_Total;

end Logging_Out;
