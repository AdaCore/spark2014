package body Amortized_Queue is pragma SPARK_Mode (On); 

   function Model (Q : in Queue) return Vector is
      RevRear : Vector := Copy (Q.Rear);
   begin
      Reverse_Elements (RevRear);
      return RevRear & Q.Front;
   end Model;

   function Tail (Q : Queue) return Queue is
      Front : Vector := Copy (Q.Front);
      Rear : Vector := Copy (Q.Rear);
   begin
      Delete_Last (Front);
      if Length (Front) < Length (Rear) then
         Reverse_Elements (Rear);
         Insert (Front, 1, Rear);
         Clear (Rear);
      end if;
      return Queue'(Front => Front, Rear => Rear);
   end Tail;

   function Enqueue (Q : in Queue; V : in Val) return Queue is
      Front : Vector := Copy (Q.Front);
      Rear : Vector := Copy (Q.Rear);
   begin
      Append (Rear, V);
      if Length (Front) < Length (Rear) then
         Reverse_Elements (Rear);
         Insert (Front, 1, Rear);
         Clear (Rear);
      end if;
      return Queue'(Front => Front, Rear => Rear);
   end Enqueue;

   function Front (Q : Queue) return Val is
   begin
      return Last_Element (Q.Front);
   end Front;

end Amortized_Queue;
