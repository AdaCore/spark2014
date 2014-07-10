package body SPARK_Off with
  SPARK_Mode => On
is
   procedure Off with SPARK_Mode => Off is
   begin
      null;
   end Off;

   procedure On is
   begin
      Off;
   end On;

end SPARK_Off;
