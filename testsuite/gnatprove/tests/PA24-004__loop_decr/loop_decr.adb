procedure Loop_Decr with SPARK_Mode is
   C : Positive := 100;
begin
   while C > 1 loop
      exit when 10 mod C = 0;
      pragma Loop_Invariant (C > 1);
      C := C - 1;
   end loop;
end Loop_Decr;
