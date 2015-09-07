with Bounded_Queue_V2;  use Bounded_Queue_V2;
with Ada.Text_IO;       use Ada.Text_IO;
procedure Bounded_Queue_Example_V2 is
-- Uses the second version of the bounded queue package

   My_Queue : Bounded_Queue_V2.Queue_Type (Max_Size => 100);
   Value    : Integer;

begin
   Clear (My_Queue);  -- Initialize queue
   for Count in Integer range 17 .. 52 loop
      Enqueue (Queue => My_Queue, Item => Count);
   end loop;
   for Count in Integer range 1 .. 5 loop
      Dequeue (Queue => My_Queue, Item => Value);
      Put_Line (Integer'Image (Value));
   end loop;
   Clear (My_Queue);
   Value := Size (My_Queue);
   Put_Line ("Size of cleared queue is " & Integer'Image (Value));
end Bounded_Queue_Example_V2;
