with Cont; use Cont;

procedure Neverending_Loop is
   use My_Sets;
begin
   for I in Cont.S loop
      Cont.Include (1);
   end loop;
end Neverending_Loop;
