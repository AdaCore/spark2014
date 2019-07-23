pragma SPARK_Mode;

with Ada.Containers.Formal_Vectors;

package List is

   Max : constant := 100;
   subtype T is integer range 1 .. Max;
   package My_Lists is new Ada.Containers.Formal_Vectors (T, Integer);
   subtype List is My_Lists.Vector (Max);
   use My_Lists;

   function Reverse_List (L : List) return List with
     Post => (for all I in First_Index (L) .. Last_Index (L) =>
                Element (L, I) = Element (Reverse_List'Result, Last_Index (L) - I + 1));

end List;
