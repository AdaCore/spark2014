procedure CVC4 (X : in out Integer) with SPARK_Mode is
begin
   if X < Integer'Last then
      X := X + 1;
   end if;
end CVC4;
