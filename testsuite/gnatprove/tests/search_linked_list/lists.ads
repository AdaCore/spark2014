with Ada.Containers.Formal_Doubly_Linked_Lists; use Ada.Containers;

package Lists is
   function My_Eq (I1, I2 : Integer) return Boolean is (I1 = I2);

   package L is new Formal_Doubly_Linked_Lists (Integer, My_Eq);
   use L;
     function Search (L : List) return Cursor with
     Contract_Cases =>
       ((for all Cu in L => Element (L, Cu) /= 0) => not Has_Element (L, Search'Result),
        (for some Cu in L => Element (L, Cu) = 0) => Element (L, Search'Result) = 0
          and then (for all Cu in First_To_Previous (L, Search'Result) => Element (L, Cu) /= 0));
       
     function Search2 (L : List) return Cursor with
       Post => (if Has_Element (L, Search2'Result) then
       (for all E of First_To_Previous (L, Search2'Result) => E /= 0));
       
     function Search2 (L : List) return Cursor is (Search (L));
end Lists;
