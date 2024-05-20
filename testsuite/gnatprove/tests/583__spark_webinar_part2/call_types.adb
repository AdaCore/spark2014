with Types_Without_RTE; use Types_Without_RTE;

procedure Call_Types is
   T : Table (0 .. 20);
begin
   for K in 1 .. 10_000_000 loop
      for I in 0 .. 10 loop
         for J in 0 .. 10 loop
            Assign (T, I, J, Element (I+J), 1);
         end loop;
      end loop;
   end loop;
end Call_Types;
