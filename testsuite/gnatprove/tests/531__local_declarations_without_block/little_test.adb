with Text_IO;
procedure Little_Test is
   type T is range 1..100;
begin
   X : T := 50;
   use Text_IO;
   for J in T loop
      if J = X then
         Put_Line (X'Image);
      end if;
   end loop;
end Little_Test;
