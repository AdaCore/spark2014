function Silly return String is
   S : String (1 .. 3);
begin
   if True then
      S := "ABC";
      return S;
   else
      declare
         X : Character := 'A';
      begin
         null;
      end;
      for Y of S loop
         null;
      end loop;
      return S;
   end if;
end;
