package body Linked_List is pragma SPARK_Mode (On);

   function Search (L : in List) return Cursor is
      Cu : Cursor := First (L);
   begin
      while Cu /= No_Element loop
         pragma Loop_Invariant
           (Has_Element (L, Cu) and then
                not Contains (Left (L, Cu), 0));

         if Element (L, Cu) = 0 then
            return Cu;
         end if;

         Next (L, Cu);
      end loop;

      return No_Element;
   end Search;

end Linked_List;
