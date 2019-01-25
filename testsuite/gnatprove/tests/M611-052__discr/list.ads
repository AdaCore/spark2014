with Ada.Containers.Formal_Vectors;

package List is

   Max : constant := 100;
   subtype T is integer range 1 .. Max;
   function Eq (E1 : T; E2 : T) return Boolean is (E1 = E2);
   package My_Lists is new Ada.Containers.Formal_Vectors (T, Integer);
   type List is new My_Lists.Vector (Max);

   function Reverse_List (L : List) return List with
     Post => (for all I in First_Index (L) .. Last_Index (L) =>
                Element (L, I) = Element (Reverse_List'Result, Last_Index (L) - I + 1));

end List;
