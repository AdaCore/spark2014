with Illegal_Type;
procedure Test_Target_Illegal with SPARK_Mode is
   type My_Acc is access Integer;

   X : My_Acc := new Integer'(3);
   Y : access Integer;

   Z : Illegal_Type.My_Acc2;
begin
   X := @;
   Y := @;
   Z := new Integer'(@.all);
end Test_Target_Illegal;
