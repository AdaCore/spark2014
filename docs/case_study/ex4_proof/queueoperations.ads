with Stacks, Queues;

package QueueOperations
is

   procedure ReverseQueue(Q : in out Queues.Queue)
      with Pre => (Queues.Size(Q) in Queues.Queue_Size);

end QueueOperations;
