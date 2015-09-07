package Bounded_Queue_V1 is
-- Version 1, details of the queue type are not hidden

   subtype Element_Type is Integer;

   type Queue_Array is array (Positive range <>) of Element_Type;
   type Queue_Type (Max_Size : Positive) is
      record
        Count : Natural;    -- Number of items
        Front : Positive;   -- Index of first item
        Rear  : Positive;   -- Index of last item
        Items : Queue_Array (1 .. Max_Size);  -- The element array
      end record;

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

end Bounded_Queue_V1;
