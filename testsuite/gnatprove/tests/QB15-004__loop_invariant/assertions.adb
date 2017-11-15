procedure Assertions with SPARK_Mode is
begin
   for J in 1 .. 10 loop
      pragma Loop_Invariant (J <= 10);
      pragma Assert (J /= 0);
      pragma Loop_Invariant (J >= 0);
end loop;
end Assertions;
