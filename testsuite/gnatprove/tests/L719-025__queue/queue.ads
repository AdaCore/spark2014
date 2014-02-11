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

   function Eq (I1 : Val; I2 : Val) return Boolean
   is (I1 = I2);

   package MyLists is new Ada.Containers.Formal_Doubly_Linked_Lists
        (Val, "=" => Eq);
   use MyLists;

   function Front (Q : in List) return Val
     with Pre  => Length (Q) > 0,
          Post => Last_Element (Q) = Front'Result;

   function Tail (Q : in List) return List
     with Pre  => Length (Q) > 0,
          Post => Strict_Equal (Tail'Result, First_To_Previous (Q, Last (Q)));

   function Enqueue (Q : in List; V : in Val) return List
     with Pre  => Length (Q) < Q.Capacity,
          Post => Length (Enqueue'Result) > 0 and then
                  First_Element (Enqueue'Result) = V and then
                  Strict_Equal (Current_To_Last (Enqueue'Result,
                    Next (Enqueue'Result, First (Enqueue'Result))), Q);

end Queue;
