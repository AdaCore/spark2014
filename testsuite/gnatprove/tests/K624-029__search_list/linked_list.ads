with Ada.Containers.Formal_Doubly_Linked_Lists;
use type Ada.Containers.Count_Type;

package Linked_List is pragma SPARK_Mode (On);

   package MyLists is new Ada.Containers.Formal_Doubly_Linked_Lists (Integer);
   use MyLists; use MyLists.Formal_Model;

   function Search (L : in List) return Cursor with
     Post => (Search'Result = No_Element and then not Contains (L, 0)) or else
     (Has_Element (L, Search'Result) and then
      Element (L, Search'Result) = 0 and then
          (for all I in 1 .. P.Get (Positions (L), Search'Result) - 1 =>
               Element (Model (L), I) /= 0));

end Linked_List;
