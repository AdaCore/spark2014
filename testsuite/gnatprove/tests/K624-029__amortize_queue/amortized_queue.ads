with Ada.Containers; use Ada.Containers;
with Ada.Containers.Formal_Vectors;

package Amortized_Queue is pragma SPARK_Mode (On);

   subtype Index is Integer range 1 .. 1_000;

   subtype Val is Integer range -2 ** 31 .. 2 ** 31 - 1;

   package My_Vectors is new Ada.Containers.Formal_Vectors
     (Index, Val);
   use My_Vectors;

   function "&" (Left, Right : Vector) return Vector with
     Pre  => Integer (Length (Left) + Length (Right)) <= Index'Last,
     Post => Length ("&"'Result) = Length (Left) + Length (Right)
     and then (for all I in 1 .. Last_Index (Left) =>
                   Element ("&"'Result, I) = Element (Left, I))
     and then (for all I in 1 .. Last_Index (Right) =>
                   Element ("&"'Result, Last_Index (Left) + I) = Element (Right, I));
   function "&" (Left : Val; Right : Vector) return Vector with
     Pre  => Integer (1 + Length (Right)) <= Index'Last,
     Post => Length ("&"'Result) = 1 + Length (Right)
     and then Element ("&"'Result, 1) = Left
     and then (for all I in 1 .. Last_Index (Right) =>
                   Element ("&"'Result, 1 + I) = Element (Right, I));
   function "&" (Left : Vector; Right : Val) return Vector with
     Pre  => Integer (Length (Left) + 1) <= Index'Last,
     Post => Length ("&"'Result) = Length (Left) + 1
     and then (for all I in 1 .. Last_Index (Left) =>
                   Element ("&"'Result, I) = Element (Left, I))
     and then Element ("&"'Result, Last_Index (Left) + 1) = Right;

   --  Implement local versions of concatenation for formal vectors, which do
   --  not define concatenation anymore.

   Capacity : constant Count_Type := Count_Type (Index'Last);

   subtype Constrained_Vector is Vector (Capacity);

   type Queue is record
      Front : Constrained_Vector;
      Rear  : Constrained_Vector;
   end record;

   function Inv (Q : in Queue) return Boolean is
     (Length (Q.Front) >= Length (Q.Rear) and then
      Q.Front.Capacity - Length (Q.Front) >= Length (Q.Rear) and then
      Q.Front.Capacity = Q.Rear.Capacity);

   function Is_Model (Q : in Queue; M : in Vector) return Boolean is
     (Length (Q.Front) + Length (Q.Rear) = Length (M) and then
      Length (M) <= Capacity and then
          (for all I in Index range 1 .. Integer (Length (Q.Rear)) =>
                Element (M, I) =
                 Element (Q.Rear, Integer (Length (Q.Rear)) - I + 1)) and then
        (for all I in Index range 1 .. Integer (Length (Q.Front)) =>
              Element (M, I + Integer (Length (Q.Rear))) =
             Element (Q.Front, I)));

   function Model (Q : in Queue) return Vector with
     Pre  => Inv (Q),
     Post => Is_Model (Q, Model'Result);

   function Front (Q : in Queue) return Val with
     Pre  => Inv (Q) and then Length (Q.Front) > 0,
     Post => Last_Element (Model (Q)) = Front'Result;

   function Tail (Q : in Queue) return Queue with
     Pre  => Inv (Q) and then Length (Q.Front) > 0,
     Post => Inv (Tail'Result) and then
     Model (Q) = Model (Tail'Result) & Last_Element (Model (Q));

   function Enqueue (Q : in Queue; V : in Val) return Queue with
     Pre  => Inv (Q) and then
     Q.Front.Capacity - Length (Q.Front) > Length (Q.Rear),
     Post => Inv (Enqueue'Result) and then
     V & Model (Q) = Model (Enqueue'Result);

end Amortized_Queue;
