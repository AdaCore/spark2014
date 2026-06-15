procedure Inject (X : Integer) with SPARK_Mode is
begin
   pragma Assert (X > 0);
end Inject;
