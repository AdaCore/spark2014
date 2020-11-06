procedure Loop_Ne (Cond : Boolean)
  with SPARK_Mode, Pure
is
   C : Natural := 1;
begin
   while C /= 0 loop
      exit when Cond;
      pragma Loop_Invariant (C /= 0);
      C := 1 / C;  --@DIVISION_CHECK:FAIL  ??? this should be provable!
   end loop;
end;
