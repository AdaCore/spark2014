procedure Assert_Twice (X : Integer) with
  SPARK_Mode
is
begin
   pragma Assert (X > 0);
   pragma Assert (X > 0);
end Assert_Twice;
