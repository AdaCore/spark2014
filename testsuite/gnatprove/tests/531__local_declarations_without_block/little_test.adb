with Text_IO;
procedure Little_Test is
begin
   type T is range 1..100;
   X : T := 50;
   use Text_IO;
   for J in T loop
      if J = X then
         Put_Line (X'Image);
      end if;
   end loop;
   procedure PL (S : String) renames Put_Line;
   PL ("Goodbye, world.");
end Little_Test;
