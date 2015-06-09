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

   procedure Search_For_In (L : in out List; P : out Cursor) with
     Post => (if Has_Element (L, P) then Element (L, P) = 0)
     and then (for all Cu in First_To_Previous (L, P) =>
                   Has_Element (L'Old, Cu) and then
                   Element (L'Old, Cu) > 0 and then
                   Element (L, Cu) = Element (L'Old, Cu) - 1);

   function Count_For_Of (L : List) return Boolean with
     Post => (if Count_For_Of'Result then
                ((for some E of L => E = 0)  and (for some E of L => E = 1)));
end For_Loops_On_Lists;
