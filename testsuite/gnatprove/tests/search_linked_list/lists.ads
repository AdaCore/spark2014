with Ada.Containers.Formal_Doubly_Linked_Lists; use Ada.Containers;

package Lists is
   package L is new Formal_Doubly_Linked_Lists (Integer);
   use L;
   function Search (L : List) return Cursor with
     Contract_Case =>
       (Name     => "all non zero",
        Mode     => Nominal,
        Requires => (for all E of L => E /= 0),
        Ensures  => not L.Has_Element (Search'Result)),
     Contract_Case =>
       (Name     => "some zero",
        Mode     => Nominal,
        Requires => (for some E of L => E = 0),
        Ensures  => L (Search'Result) = 0
          and then (for all E of L.Left (Search'Result) => E /= 0));
end Lists;
