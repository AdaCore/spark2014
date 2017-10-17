procedure Induction (X : out Integer) is
begin
   X := 0;
   for J in 1 .. 10 loop
      X := X + 1;
   end loop;
end Induction;
