with Ada.Containers.Formal_Vectors;

package List is

   subtype T is integer range 1 .. 10;
   function Eq (E1 : T; E2 : T) return Boolean is
     (E1 = E2);
   package My_Lists is new Ada.Containers.Formal_Vectors (T, Integer, Eq);
  type List is new My_Lists.Vector (10);

  function Reverse_List (L : List) return List with
     Post => (for all I in T => Element (L, I) = Element (Reverse_List'Result, T'Last - I + 1));

end List;
