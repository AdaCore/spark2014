package Queues is

   type Queue is limited private;

   function EmptyQueue(Q : in Queue) return Boolean;

   function FullQueue(Q : in Queue) return Boolean;

   procedure ClearQueue(Q : out Queue);

   procedure EnQueue(Q : in out Queue; X : in Integer);

   procedure DeQueue(Q : in out Queue; X : out Integer);

private
   type Queue is new Integer;
end Queues;
