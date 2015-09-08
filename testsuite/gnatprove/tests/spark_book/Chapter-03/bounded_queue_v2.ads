package Bounded_Queue_V2 is
-- Version 2, details of the queue type are hidden

   subtype Element_Type is Integer;

   type Queue_Type (Max_Size : Positive) is private
     with Default_Initial_Condition;

   function Full (Queue : in Queue_Type) return Boolean;

   function Empty (Queue : in Queue_Type) return Boolean;

   function Size (Queue : in Queue_Type) return Natural;

   function First_Element (Queue : in Queue_Type) return Element_Type
      with
         Pre => not Empty (Queue);

   function Last_Element (Queue : in Queue_Type) return Element_Type
      with
         Pre => not Empty (Queue);

   procedure Clear (Queue : in out Queue_Type)
      with
         Post => Empty (Queue) and then Size (Queue) = 0;

   procedure Enqueue (Queue : in out Queue_Type;
                      Item  : in     Element_Type)
      with
         Pre  => not Full (Queue),
         Post => not Empty (Queue) and then
                 Size (Queue) = Size (Queue'Old) + 1 and then
                 Last_Element (Queue) = Item;

   procedure Dequeue (Queue : in out Queue_Type;
                      Item  :    out Element_Type)
      with
        Pre  => not Empty (Queue),
        Post => Item = First_Element (Queue'Old) and then
                Size (Queue) = Size (Queue'Old) - 1;

private

   type Queue_Array is array (Positive range <>) of Element_Type;
   type Queue_Type (Max_Size : Positive) is
      record
         Count : Natural  := 0;   -- Number of items
         Front : Positive := 1;   -- Index of first item
         Rear  : Positive := Max_Size;  -- Index of last item
         Items : Queue_Array (1 .. Max_Size);  -- The element array
      end record;

end Bounded_Queue_V2;
