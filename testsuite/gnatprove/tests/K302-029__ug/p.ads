package P with SPARK_Mode => On is
   X : access Boolean;
   procedure P0 with SPARK_Mode => Off;
end P;
