package body Amortized_Queue is pragma SPARK_Mode (On);

   function "&" (Left, Right : Vector) return Vector is
   begin
      return Result : Vector (Capacity => Left.Capacity) do
        for Idx in First_Index (Left) .. Last_Index (Left) loop
           Append (Result, Element (Left, Idx));
        end loop;
        for Idx in First_Index (Right) .. Last_Index (Right) loop
           Append (Result, Element (Right, Idx));
        end loop;
      end return;
   end "&";

   function "&" (Left : Integer; Right : Vector) return Vector is
   begin
      return Result : Vector (Capacity => Right.Capacity) do
        Append (Result, Left);
        for Idx in First_Index (Right) .. Last_Index (Right) loop
           Append (Result, Element (Right, Idx));
        end loop;
      end return;
   end "&";

   function "&" (Left : Vector; Right : Integer) return Vector is
   begin
      return Result : Vector (Capacity => Left.Capacity) do
        for Idx in First_Index (Left) .. Last_Index (Left) loop
           Append (Result, Element (Left, Idx));
        end loop;
        Append (Result, Right);
      end return;
   end "&";

   procedure Reverse_Insert (Front : out Vector; Rear : in out Vector) is
   begin
      for Idx in reverse First_Index (Rear) .. Last_Index (Rear) loop
         Append (Front, Element (Rear, Idx));
      end loop;
   end Reverse_Insert;

   function Model (Q : in Queue) return Vector is
      RevRear : Vector := Copy (Q.Rear);
   begin
      Reverse_Elements (RevRear);
      return RevRear & Q.Front;
   end Model;

   function Tail (Q : Queue) return Queue is
   begin
      return Result : Queue := (Front => Copy (Q.Front), Rear => Copy (Q.Rear)) do
        Delete_Last (Result.Front);
        if Length (Result.Front) < Length (Result.Rear) then
           Reverse_Insert (Result.Front, Result.Rear);
        end if;
      end return;
   end Tail;

   function Enqueue (Q : in Queue; V : in Val) return Queue is
   begin
      return Result : Queue := (Front => Copy (Q.Front), Rear => Copy (Q.Rear)) do
        Append (Result.Rear, V);
        if Length (Result.Front) < Length (Result.Rear) then
           Reverse_Insert (Result.Front, Result.Rear);
        end if;
      end return;
   end Enqueue;

   function Front (Q : Queue) return Val is
   begin
      return Last_Element (Q.Front);
   end Front;

end Amortized_Queue;
