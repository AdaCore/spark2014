procedure Bad_Induction (X : out Integer) is
begin
   for J in 1 .. 10 loop
      X := X + 1;
   end loop;
end Bad_Induction;
