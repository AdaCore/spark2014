package Abnormal_Terminations with
  SPARK_Mode
is

   G1, G2 : Integer := 0;

   procedure Check_OK (OK : Boolean) with
     Global => (Output => G1),
     Pre    => OK;

end Abnormal_Terminations;
