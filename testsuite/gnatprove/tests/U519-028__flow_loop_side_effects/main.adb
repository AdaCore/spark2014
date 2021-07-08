procedure Main with Global => null is
   X : Integer := 3;
begin
   if False then
      for J in 1 .. X loop
         X := X + 1;
      end loop;
   end if;
end Main;
