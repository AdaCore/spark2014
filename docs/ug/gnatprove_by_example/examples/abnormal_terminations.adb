package body Abnormal_Terminations with
  SPARK_Mode
is

   procedure Check_OK (OK : Boolean) is
   begin
      if OK then
         G1 := 1;
      else
         G2 := 1;
         raise Program_Error;
      end if;
   end Check_OK;

end Abnormal_Terminations;
