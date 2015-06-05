with Ada.Containers; use Ada.Containers;
with Ada.Containers.Formal_Doubly_Linked_Lists;
package For_Loops_On_Lists with SPARK_Mode is
   package My_Lists is new Formal_Doubly_Linked_Lists
     (Element_Type => Natural);
   use My_Lists;

   function Search_0_For_In (L : List) return Cursor with
     Post => (Has_Element (L, Search_0_For_In'Result) and then
                  Element (L, Search_0_For_In'Result) = 0)
     or else (Search_0_For_In'Result = No_Element and then
                (for all E of L => E /= 0));

   function Contains_0_For_Of (L : List) return Boolean with
     Post => (if Contains_0_For_Of'Result then (for some E of L => E = 0));
end For_Loops_On_Lists;
