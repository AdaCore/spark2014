package body P is
   -- Does not return on some paths
   function F1 return Integer is
   begin
      if C = 0 then
         loop
            null;
         end loop;
      else
         return C;
      end if;
   end;

   -- Does not return on any path
   function F2 return Integer is
   begin
      if C = 0 then
         loop
            null;
         end loop;
         return 0;
      else
         loop
            null;
         end loop;
      end if;
   end;

   function F3 return Integer is
   begin
      if C = 0 then
         return 1;
      else
         return 0;
      end if;
   end;
end;
