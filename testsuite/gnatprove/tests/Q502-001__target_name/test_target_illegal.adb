procedure Test_Target_Illegal with SPARK_Mode is
   type My_Acc is access Integer;

   X : My_Acc := new Integer'(3);
   Y : access Integer;
begin
   X := @;
   Y := @;
end Test_Target_Illegal;
