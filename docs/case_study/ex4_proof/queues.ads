package Queues is

   type Queue is private; -- removed limited to be able to use 'Old in Post

   Max_Count : constant Integer := 100;
   subtype Queue_Size is Natural range 0 .. Max_Count;

   -- Proof function that should not be called in code.
   function Size (Q : in Queue) return Queue_Size;

   function EmptyQueue(Q : in Queue) return Boolean
      with Post => (EmptyQueue'Result = (Size(Q) = 0));

   function FullQueue(Q : in Queue) return Boolean;

   procedure ClearQueue(Q : out Queue);

   procedure EnQueue(Q : in out Queue; X : in Integer)
      with pre => (Size (Q) in 0 .. 99),
           post => (Size(Q) = Size(Q'Old) + 1);

   procedure DeQueue(Q : in out Queue; X : out Integer)
      with pre => (Size (Q) in 1 .. 100),
           post => (Size(Q) = Size(Q'Old) - 1);

private
   subtype Count_T is Integer range 0 .. Max_Count;
   subtype Index_T is Count_T range 1 .. Max_Count;
   type Array_T is array (Index_T) of Integer;
   type Queue is record
      The_Begin : Index_T;
      The_End   : Index_T;
      The_Queue : Array_T;
   end record;
end Queues;
