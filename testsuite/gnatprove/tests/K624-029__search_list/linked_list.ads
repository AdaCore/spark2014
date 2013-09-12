with Ada.Containers.Formal_Doubly_Linked_Lists;

package Linked_List is pragma SPARK_Mode (On);

   function Eq (I1, I2 : Integer) return Boolean is (I1 = I2);

   package MyLists is new Ada.Containers.Formal_Doubly_Linked_Lists
     (Integer, "=" => Eq);
   use MyLists;

   function Search (L : in List) return Cursor with
     Post => (Search'Result = No_Element and then  not Contains (L, 0)) or else
     (Has_Element (L, Search'Result) and then
      Element (L, Search'Result) = 0 and then
          not Contains (Left (L, Search'Result), 0));

end Linked_List;
