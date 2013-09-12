with Ada.Containers.Formal_Doubly_Linked_Lists;
with Ada.Containers; use Ada.Containers;
package Queue is pragma SPARK_Mode (On);

   subtype Val is Integer range -2 ** 31 .. 2 ** 31 - 1;

   function Eq (I1 : Val; I2 : Val) return Boolean
   is (I1 = I2);

   package MyLists is new Ada.Containers.Formal_Doubly_Linked_Lists
        (Val, "=" => Eq);
   use MyLists;

   function Front (Q : in List) return Val with
     Pre  => Length (Q) > 0,
     Post => Last_Element (Q) = Front'Result;

   function Tail (Q : in List) return List with
     Pre  => Length (Q) > 0,
     Post => Strict_Equal (Tail'Result, Left (Q, Last (Q)));

   function Enqueue (Q : in List; V : in Val) return List with
     Pre  => Length (Q) < Q.Capacity,
     Post => Length (Enqueue'Result) > 0 and then
     First_Element (Enqueue'Result) = V and then
      Strict_Equal (Right (Enqueue'Result,
                    Next (Enqueue'Result, First (Enqueue'Result))), Q);

end Queue;
