with Ada.Containers.Formal_Doubly_Linked_Lists; use Ada.Containers;

package Lists is
   package L is new Formal_Doubly_Linked_Lists (Integer);
   use L;
   function Search (L : List) return Cursor with
     Contract_Case =>
       (Name     => "all non zero",
        Mode     => Nominal,
        Requires => (for all C in L.Iterate => Element (L, C) /= 0),
        Ensures  => not Has_Element (L, Search'Result)),
     Contract_Case =>
       (Name     => "some zero",
        Mode     => Nominal,
        Requires => (for some C in L.Iterate => Element (L, C) = 0),
        Ensures  => Element (L, Search'Result) = 0
          and then (for all C in Left (L, Search'Result).Iterate =>
                      Element (L, C) /= 0));
end Lists;
