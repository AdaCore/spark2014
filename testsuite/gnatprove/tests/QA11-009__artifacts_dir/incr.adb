procedure Incr (X : in out Integer) with SPARK_Mode is
begin
   X := X + 1;
end Incr;
