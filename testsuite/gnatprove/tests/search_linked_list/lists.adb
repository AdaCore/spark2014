package body Lists with SPARK_Mode is
   function Search (L : List) return Cursor is
      C : Cursor := First (L);
   begin
      while Has_Element (L, C) loop
         pragma Loop_Invariant
           (for all I in 1 .. P.Get (Positions (L), C) - 1 => Element (Model (L), I) /= 0);
         if Element (L, C) = 0 then
            return C;
         end if;
         Next (L, C);
      end loop;
      return No_Element;
   end Search;
end Lists;
