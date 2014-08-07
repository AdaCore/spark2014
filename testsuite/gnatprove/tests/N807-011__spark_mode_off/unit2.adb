package body Unit2 with
  SPARK_Mode => On
is
   procedure P with
     SPARK_Mode => Off
   is
   begin
      Unit1.P;
   end P;

   procedure Q is
   begin
      P;
   end Q;
end Unit2;
