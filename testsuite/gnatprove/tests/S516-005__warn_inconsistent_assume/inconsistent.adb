procedure Inconsistent (X : Natural) with SPARK_Mode is
begin
   pragma Assume (X = -1);
end Inconsistent;
