package body Lists is
   function Search (L : List) return Cursor is
      C : Cursor;
   begin
      C := First (L);
      while Has_Element (L, C) loop
         pragma Assert (for all D in Left (L, C).Iterate =>
                          Element (L, D) /= 0);
         if Element (L, C) = 0 then
            return C;
         end if;
         Next (L, C);
      end loop;
      return No_Element;
   end Search;
end Lists;
