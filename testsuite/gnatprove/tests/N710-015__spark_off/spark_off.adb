package body SPARK_Off with
  SPARK_Mode => On
is
   procedure Proc_Off with SPARK_Mode => Off is
   begin
      null;
   end Proc_Off;

   procedure Proc_On is
   begin
      Proc_Off;
   end Proc_On;

end SPARK_Off;
