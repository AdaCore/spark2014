with Ada.Containers.Formal_Doubly_Linked_Lists;
with Ada.Containers; use Ada.Containers;

package Queue
  with SPARK_Mode
is
   ----------------------------------------------------
   --         SPARK 2014 - Queue Example             --
   --                                                --
   -- This example illustrates the use of the formal --
   -- container libraries in SPARK 2014.  In this    --
   -- example the Formal_Doubly_Linked_Lists package --
   -- is used to implement a container for a queue   --
   -- of Integers.                                   --
   ----------------------------------------------------

   subtype Val is Integer range -2 ** 31 .. 2 ** 31 - 1;

   package MyLists is new Ada.Containers.Formal_Doubly_Linked_Lists (Val);
   use MyLists; use MyLists.Formal_Model;

   function Front (Q : in List) return Val
     with Pre  => Length (Q) > 0,
          Post => Last_Element (Q) = Front'Result;

   function Tail (Q : in List) return List with
     Pre  => Length (Q) > 0,
     Post => Length (Tail'Result) = Length (Q) - 1
     and Model (Tail'Result) < Model (Q);

   function Enqueue (Q : in List; V : in Val) return List with
     Pre  => Length (Q) < Q.Capacity,
     Post => Length (Enqueue'Result) = Length (Q) + 1
     and First_Element (Enqueue'Result) = V
     and (for all I in 2 .. Length (Q) + 1 =>
             Element (Model (Enqueue'Result), I) = Element (Model (Q), I - 1));

end Queue;
