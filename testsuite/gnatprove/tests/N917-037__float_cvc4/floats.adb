procedure Floats with
  SPARK_Mode
is
   Dummy : constant Float := 1.0;
begin
   pragma Assert (False);  --  @ASSERT:FAIL
end Floats;
