package body Lists is 
   function Search (L : List) return Cursor is
   begin
      for C in Iterate (L) loop
         pragma Assert (for all E of L.Left (C) => E /= 0);
         if L (C) = 0 then
            return C;
         end if;
      end loop;
      return No_Element;
   end Search;
end Lists;
