package Queues is

   type Queue is limited private;

   Max_Count : constant Integer := 100;

   subtype Queue_Size is Natural range 0 .. Max_Count;

   --# function Size (Q : in Queue) return Queue_Size;

   function EmptyQueue(Q : in Queue) return Boolean;
   --# return Size(Q) = 0;

   function FullQueue(Q : in Queue) return Boolean;
   --# return Size(Q) = Max_Count;

   procedure ClearQueue(Q : out Queue);
   --# post Size(Q) = 0;

   procedure EnQueue(Q : in out Queue; X : in Integer);
   --# pre  Size(Q) < Max_Count;
   --# post Size(Q) = Size(Q~) + 1;

   procedure DeQueue(Q : in out Queue; X : out Integer);
  --# pre  Size(Q) >= 1;
  --# post Size(Q) = Size(Q~) - 1;

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
