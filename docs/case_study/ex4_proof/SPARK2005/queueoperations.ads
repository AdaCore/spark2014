with Stacks, Queues;
--# inherit Stacks, Queues;

package QueueOperations
is

   procedure ReverseQueue(Q : in out Queues.Queue);
   --# pre (Queues.Size(Q) in 1 .. Queues.Max_Count);

end QueueOperations;
