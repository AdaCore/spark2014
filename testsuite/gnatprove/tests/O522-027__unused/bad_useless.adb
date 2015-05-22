procedure Bad_Useless (X : in out Integer)
  with SPARK_Mode
is
   Tmp : Integer;
begin
   Tmp := X;
   for J in 1 .. 10 loop
      X := X + 1;
      pragma Loop_Invariant (X = Tmp + J);
   end loop;
end Bad_Useless;
