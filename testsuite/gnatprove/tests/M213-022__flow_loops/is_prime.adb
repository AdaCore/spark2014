procedure Is_Prime (N : Positive;
                    P : out Boolean)
is
begin

   for I in Positive range 2 .. N / 2 loop
      if N mod I = 0 then
         P := False;
         return;
      end if;
   end loop;
   P := True;

end Is_Prime;
