with Ada.Containers.Formal_Doubly_Linked_Lists; use Ada.Containers;

package Lists is 
   package L is new Formal_Doubly_Linked_Lists (Integer);
   use L;
   function Search (L : List) return Cursor with
     Contract_Cases =>
       ((for all E of L => E /= 0) => not L.Has_Element (Search'Result),
        (for some E of L => E = 0) => L (Search'Result) = 0
          and then (for all E of L.Left (Search'Result) => E /= 0));
end Lists;
