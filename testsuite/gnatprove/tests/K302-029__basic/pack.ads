package Pack is

   X : Boolean;

   type Acc is access Integer;
   Y : Acc;

   procedure P0 with SPARK_Mode => On;
   procedure P1 with SPARK_Mode => On;
   procedure P2 with SPARK_Mode => On;
   procedure P3 with SPARK_Mode => Off;
   procedure P4 with SPARK_Mode => On;
   procedure P5 with SPARK_Mode => On;

end;
