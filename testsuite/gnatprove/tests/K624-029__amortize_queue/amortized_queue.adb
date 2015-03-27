package body Amortized_Queue is pragma SPARK_Mode (On);

   function "&" (Left, Right : Vector) return Vector is
   begin
      return Result : Vector (Capacity => Length (Left) + Length (Right)) do
         for Idx in 1 .. Last_Index (Left) loop
            Append (Result, Element (Left, Idx));
            pragma Loop_Invariant(Integer (Length (Result)) = Idx);
            pragma Loop_Invariant
              (for all I in 1 .. Idx =>
                   Element (Result, I) = Element (Left, I));
         end loop;
         for Idx in 1 .. Last_Index (Right) loop
            Append (Result, Element (Right, Idx));
            pragma Loop_Invariant(Integer (Length (Result)) = Last_Index (Left) + Idx);
            pragma Loop_Invariant
              (for all I in 1 .. Last_Index (Left) =>
                   Element (Result, I) = Element (Left, I));
            pragma Loop_Invariant
              (for all I in 1 .. Idx =>
                   Element (Result, Last_Index (Left) + I) = Element (Right, I));
         end loop;
      end return;
   end "&";

   function "&" (Left : Integer; Right : Vector) return Vector is
   begin
      return Result : Vector (Capacity => 1 + Length (Right)) do
         Append (Result, Left);
         for Idx in First_Index (Right) .. Last_Index (Right) loop
            Append (Result, Element (Right, Idx));
            pragma Loop_Invariant(Integer (Length (Result)) = 1 + Idx);
            pragma Loop_Invariant (Element (Result, 1) = Left);
            pragma Loop_Invariant
              (for all I in 1 .. Idx =>
                 Element (Result, 1 + I) = Element (Right, I));
         end loop;
      end return;
   end "&";

   function "&" (Left : Vector; Right : Integer) return Vector is
   begin
      return Result : Vector (Capacity => Length (Left) + 1) do
         for Idx in First_Index (Left) .. Last_Index (Left) loop
            Append (Result, Element (Left, Idx));
            pragma Loop_Invariant(Integer (Length (Result)) = Idx);
            pragma Loop_Invariant
              (for all I in 1 .. Idx =>
                 Element (Result, I) = Element (Left, I));
        end loop;
        Append (Result, Right);
      end return;
   end "&";

   procedure Reverse_Insert (Front : in out Constrained_Vector;
                             Rear : in out Constrained_Vector;
                             OFront : in Constrained_Vector;
                             ORear : in Constrained_Vector) with
     Pre => Capacity - Length (Front) > Length (Rear)
     and then Front = OFront and then Rear = Orear,
     Post => Length (Front) = Length (OFront) + Length (ORear)
     and then Length (Rear) = 0
     and then (for all I in 1 .. Last_Index (OFront) =>
                   Element (Front, I) = Element (OFront, I))
     and then (for all I in 1 .. Last_Index (ORear) =>
                 Element (Front, Last_Index (Front) + 1 - I) = Element (ORear, I))
   is
   begin
      for Idx in reverse 1 .. Last_Index (Rear) loop
         Append (Front, Element (Rear, Idx));
         pragma Loop_Invariant(Integer (Length (Front)) = Integer (Length (OFront)) + Last_Index (Rear) - Idx + 1);
         pragma Loop_Invariant
           (for all I in 1 .. Last_Index (OFront) =>
              Element (Front, I) = Element (OFront, I));
         pragma Loop_Invariant
           (for all I in Idx .. Last_Index (Rear) =>
              Element (Front, Last_Index (Front) + Idx - I) = Element (Rear, I));
      end loop;
      Clear (Rear);
   end Reverse_Insert;

   function Model (Q : in Queue) return Vector is
      RevRear : Vector := Copy (Q.Rear);
   begin
      Reverse_Elements (RevRear);
      return RevRear & Q.Front;
   end Model;

   function Tail (Q : Queue) return Queue is
   begin
      return Result : Queue := (Front => Copy (Q.Front, Capacity),
                                Rear => Copy (Q.Rear, Capacity)) do
        Delete_Last (Result.Front);
        if Length (Result.Front) < Length (Result.Rear) then
           Reverse_Insert (Result.Front, Result.Rear, Copy (Result.Front, Capacity), Copy (Result.Rear, Capacity));
        end if;
      end return;
   end Tail;

   function Enqueue (Q : in Queue; V : in Val) return Queue is
   begin
      return Result : Queue := (Front => Copy (Q.Front, Capacity),
                                Rear => Copy (Q.Rear, Capacity)) do
        Append (Result.Rear, V);
        if Length (Result.Front) < Length (Result.Rear) then
           Reverse_Insert (Result.Front, Result.Rear, Copy (Result.Front, Capacity), Copy (Result.Rear, Capacity));
        end if;
      end return;
   end Enqueue;

   function Front (Q : Queue) return Val is
   begin
      return Last_Element (Q.Front);
   end Front;

end Amortized_Queue;
