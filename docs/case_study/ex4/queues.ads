package Queues is

   type Queue is limited private;

   function EmptyQueue(Q : in Queue) return Boolean;

   function FullQueue(Q : in Queue) return Boolean;

   procedure ClearQueue(Q : out Queue);

   procedure EnQueue(Q : in out Queue; X : in Integer)
     with pre => not FullQueue (Q);

   procedure DeQueue(Q : in out Queue; X : out Integer)
     with pre => not EmptyQueue (Q);

private
   Max_Count : constant Integer := 100;
   subtype Count_T is Integer range 0 .. Max_Count;
   subtype Index_T is Count_T range 1 .. Max_Count;
   type Array_T is array (Index_T) of Integer;
   type Queue is record
      The_Begin : Index_T;
      The_End   : Index_T;
      The_Queue : Array_T;
   end record;
end Queues;
