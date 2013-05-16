package body Queues is

   function EmptyQueue(Q : in Queue) return Boolean
   is (Q.The_Begin = Q.The_End);

   function FullQueue(Q : in Queue) return Boolean
   is ((Q.The_Begin mod Max_Count) + 1 = Q.The_End);

   procedure ClearQueue(Q : out Queue)
   is
   begin
      Q.The_Queue := Array_T'(others => 0);
      Q.The_Begin := Index_T'First;
      Q.The_End   := Index_T'First;
   end ClearQueue;

   procedure EnQueue(Q : in out Queue; X : in Integer) is
   begin
      Q.The_Begin := (Q.The_Begin mod Max_Count) + 1;
      Q.The_Queue (Q.The_Begin) := X;
   end EnQueue;

   procedure DeQueue(Q : in out Queue; X : out Integer) is
   begin
      X := Q.The_Queue (Q.The_End);
      Q.The_End := (Q.The_End mod Max_Count) + 1;
   end DeQueue;

end Queues;
