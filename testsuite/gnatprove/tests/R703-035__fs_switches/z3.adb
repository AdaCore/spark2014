procedure Z3 (X : in out Integer) with SPARK_Mode is
begin
   if X < Integer'Last then
      X := X + 1;
   end if;
end Z3;
