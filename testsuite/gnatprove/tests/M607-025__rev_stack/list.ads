with Ada.Containers.Formal_Vectors;

package List is
   pragma Spark_Mode (On);

   Max : constant := 100;
   subtype T is Integer range 1 .. Max;
   package My_Lists is new Ada.Containers.Formal_Vectors (T, Integer);
   type List is new My_Lists.Vector (Max);

   function Reverse_List (L : List) return List with
     Post => (for all I in First_Index (L) .. Last_Index (L) =>
                  Element (L, I) = Element (Reverse_List'Result,
                  Last_Index (L) - I + First_Index (L)));

end List;
