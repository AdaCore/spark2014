with Ada.Containers.Formal_Doubly_Linked_Lists; use Ada.Containers;

----------------------------------------------------
-- SPARK 2014 - Linked List Search Example        --
--                                                --
-- This example illustrates the use of Pre, Post  --
-- and Contract_Cases aspects involving a formal  --
-- doubly linked list in SPARK 2014.              --
----------------------------------------------------

package Lists with SPARK_Mode is
   function My_Eq (I1, I2 : Integer) return Boolean is (I1 = I2);

   package L is new Formal_Doubly_Linked_Lists (Integer);
   use L; use Formal_Model;
     function Search (L : List) return Cursor with
     Contract_Cases =>
       ((for all Cu in L => Element (L, Cu) /= 0) => not Has_Element (L, Search'Result),
        (for some Cu in L => Element (L, Cu) = 0) => Element (L, Search'Result) = 0
          and then (for all I in 1 .. P.Get (Positions (L), Search'Result) - 1 => Element (Model (L), I) /= 0));

     function Search2 (L : List) return Cursor with
       Post => (if Has_Element (L, Search2'Result) then
       (for all Cu in L => (if P.Get (Positions (L), Cu) < P.Get (Positions (L), Search2'Result) then Element (L, Cu) /= 0)));

     function Search2 (L : List) return Cursor is (Search (L));
end Lists;
