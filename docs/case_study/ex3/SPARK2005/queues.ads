package Queues is

   type Queue is limited private;

   function EmptyQueue(Q : in Queue) return Boolean;

   function FullQueue(Q : in Queue) return Boolean;

   procedure ClearQueue(Q : out Queue);
   --# derives Q from ;

   procedure EnQueue(Q : in out Queue; X : in Integer);
   --# derives Q from Q, X;

   procedure DeQueue(Q : in out Queue; X : out Integer);
   --# derives Q from Q &
   --#         X from Q;

private
--# hide Queues
end Queues;
