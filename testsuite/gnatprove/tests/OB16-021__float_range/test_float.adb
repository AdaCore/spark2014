procedure Test_Float (X : Float; Y : Integer)
  with SPARK_Mode
is
begin
   pragma Assert (X in -1.0 .. 1.0);
   pragma Assert (Y in -1 .. 1);
end Test_Float;
