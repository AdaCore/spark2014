package body QueueOperations
is

   procedure ReverseQueue(Q : in out Queues.Queue)
   is
      S: Stacks.Stack;
      X: Integer;
      Count : Natural := 0;
   begin
      Stacks.ClearStack(S);
      while not Queues.EmptyQueue(Q) loop
         --# assert ((Queues.Size(Q) in 1 .. Queues.Max_Count) and
         --#         (Stacks.Size(S) = Count) and
         --#         (Stacks.Size(S) >= 0) and
         --#         (Count = Queues.Size(Q~) - Queues.Size(Q)));
         Queues.DeQueue(Q, X);
         Stacks.Push(S, X);
         Count := Count + 1;
      end loop;
      while Count > 0 loop
         Stacks.Pop(S, X);
         Queues.EnQueue(Q, X);
         Count := Count - 1;
         --# assert (Stacks.Size(S) = Count) and
         --#        (Stacks.Size(S) >= 0) and
         --#        (Queues.Size(Q) in 1 .. Queues.Max_Count) and
         --#        (Queues.Size(Q) = Queues.Size(Q~) - Count);
      end loop;
   end ReverseQueue;

end QueueOperations;
