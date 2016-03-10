procedure Main is

   subtype Pos is Integer with Dynamic_Predicate => False;

begin
   for X in Pos (1) .. Pos (3) loop
      null;
   end loop;
end;
