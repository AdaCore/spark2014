--  Integer_Lists : singly linked list of integers, based on POINTERS.
--
--  In SPARK, pointers (access types) obey an "ownership" model
--  Rust style : each cell on the heap has exactly one owner. An
--  assignment transfers ownership (a "move"), which forbids any
--  aliasing and makes the proof possible.
--
--  The properties are described with the ghost "model" function Length, defined
--  by recursion. To prove termination of these recursive functions over
--  a pointer structure, one uses Subprogram_Variant (Structural => L) :
--  each recursive call descends into a strictly smaller sub-structure.
--
--  Length returns a Big_Natural (unbounded mathematical integer) from the
--  SPARK library Ada.Numerics.Big_Numbers.Big_Integers. Since this type has
--  no upper bound, there is no possible overflow : no longer any need for
--  the guard "= Natural'Last" nor the preconditions "Length (L) < Natural'Last".

with Ada.Numerics.Big_Numbers.Big_Integers;
use Ada.Numerics.Big_Numbers.Big_Integers;

package Integer_Lists with SPARK_Mode is

   type Cell;
   type List is access Cell;
   type Cell is record
      Value : Integer;
      Next  : List;
   end record;


   ---------------------------------------------------------------------------
   --  Model function (ghost) : length of the list.
   ---------------------------------------------------------------------------

   function Length (L : access constant Cell) return Big_Natural is
     (if L = null then 0
      else Length (L.Next) + 1)
   with Ghost,
        Subprogram_Variant => (Structural => L);
   --  Big_Natural is unbounded : no overflow, so no guard.

   ---------------------------------------------------------------------------
   --  Search : recursive function (read-only traversal).
   ---------------------------------------------------------------------------

   function Contains (L : access constant Cell; E : Integer) return Boolean is
     (if L = null then False
      elsif L.Value = E then True
      else Contains (L.Next, E))
   with Subprogram_Variant => (Structural => L);

   ---------------------------------------------------------------------------
   --  Structural equality : two lists are equal when they have the same
   --  length and the same elements in the same order.
   ---------------------------------------------------------------------------

   function Equal (L1, L2 : access constant Cell) return Boolean is
     (if L1 = null or else L2 = null then L1 = null and then L2 = null
      else L1.Value = L2.Value and then Equal (L1.Next, L2.Next))
   with Subprogram_Variant => (Structural => L1);

   ---------------------------------------------------------------------------
   --  Operations, each with its proven property.
   ---------------------------------------------------------------------------

   function Copy (L : access constant Cell) return List
     with Post => Length (Copy'Result) = Length (L)
     and then Equal (Copy'Result, L) and then Equal(L,Copy'Result)
     and then (if L/=Null then Last_elem(L) = Last_elem(Copy'Result)) ,
          Subprogram_Variant => (Structural => L);
   --  Deep copy : returns a fresh list (fresh cells) equal to L
   --  (same elements, same order).  Essential in SPARK as soon as one wants two
   --  independent lists : the ownership model forbids sharing the
   --  cells.

   function Last_elem (L : access constant Cell) return Integer is
     (if L.Next = null then L.Value else Last_elem (L.Next))
   with Pre => L /= null,
        Subprogram_Variant => (Structural => L);
   --  Expression function in the SPEC : its definition is visible to the provers
   --  of all clients (e.g. Kruskal), which can thus compute Last_elem
   --  of a one-element list (= its Value).



   --procedure Push (L : in out List; E : Integer)
   --  with Post => Length (L) = Length (L)'Old + 1
       --           and then L /= null
     --and then L.Value = E ;
       --  Inserts E at head. No precondition any more : Big_Natural does not saturate.

      function Push (L : List; Item : Integer) return List
   with Post =>
          Push'Result /= null
          and then Push'Result.Value = Item
       and then Equal (Push'Result.Next, L)
       and then (if L /= Null then Last_elem(L) = Last_elem(Push'Result) )
       and then Equal (L,Push'Result.Next);



   procedure Pop (L : in out List)
     with Pre  => L /= null,
          Post => Length (L) = Length (L)'Old - 1;
   --  Removes (and frees) the head cell.

   procedure Free_List (L : in out List)
     with Post => L = null,
          Subprogram_Variant => (Structural => L);
   --  Frees the whole list recursively (mandatory : otherwise memory leak,
   --  which GNATprove detects automatically).

end Integer_Lists;
