with Bounded_Queue;
with Ada.Text_IO;   use Ada.Text_IO;
procedure Bounded_Queue_Example is
   -- Uses the generic version of the bounded queue package

   -- Instantiate a queue package with character elements
   package Char_Queue is new Bounded_Queue (Element_Type => Character);
   use Char_Queue;

   My_Queue : Char_Queue.Queue_Type (Max_Size => 100);
   Value    : Character;

begin
   Clear (My_Queue);  -- Initialize queue
   for Char in Character range 'f' .. 'p' loop
      Enqueue (Queue => My_Queue, Item => Char);
   end loop;
   for Count in Integer range 1 .. 5 loop
      Dequeue (Queue => My_Queue, Item => Value);
      Put (Value);
      New_Line;
   end loop;
   Clear (My_Queue);
   Put_Line ("Size of cleared queue is " & Integer'Image (Size (My_Queue)));
end Bounded_Queue_Example;
