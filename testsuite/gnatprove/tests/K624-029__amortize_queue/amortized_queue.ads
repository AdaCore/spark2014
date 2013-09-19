with Ada.Containers; use Ada.Containers;
with Ada.Containers.Formal_Vectors;

package Amortized_Queue is pragma SPARK_Mode (On);

   subtype Index is Integer range 1 .. 1_000;

   subtype Val is Integer range -2 ** 31 .. 2 ** 31 - 1;

   function Eq (I1 : Val; I2 : Val) return Boolean is
     (I1 = I2);

   package My_Vectors is new Ada.Containers.Formal_Vectors
     (Index, Val, Eq);
   use My_Vectors;

   Capacity : constant Count_Type := Count_Type (Index'Last);

   type Queue is record
      Front : Vector (Capacity);
      Rear  : Vector (Capacity);
   end record;

   function Inv (Q : in Queue) return Boolean is
     (Length (Q.Front) >= Length (Q.Rear) and then
      Q.Front.Capacity - Length (Q.Front) >= Length (Q.Rear) and then
      Q.Front.Capacity = Q.Rear.Capacity);

   function Is_Model (Q : in Queue; M : in Vector) return Boolean is
     (Length (Q.Front) + Length (Q.Rear) = Length (M) and then
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
     Post => (if is_Model (Q, Model (Q)) then
                Last_Element (Model (Q)) = Front'Result);

   function Tail (Q : in Queue) return Queue with
     Pre  => Inv (Q) and then Length (Q.Front) > 0,
     Post => Inv (Tail'Result) and then
     (if is_Model (Q, Model (Q)) and is_Model (Tail'Result, Model (Tail'Result)) then
        Model (Q) = Model (Tail'Result) & Last_Element (Model (Q)));

   function Enqueue (Q : in Queue; V : in Val) return Queue with
     Pre  => Inv (Q) and then
     Q.Front.Capacity - Length (Q.Front) > Length (Q.Rear),
     Post => Inv (Enqueue'Result) and then
     (if is_Model (Q, Model (Q)) and is_Model (Enqueue'Result, Model (Enqueue'Result)) then
        V & Model (Q) = Model (Enqueue'Result));

end Amortized_Queue;
