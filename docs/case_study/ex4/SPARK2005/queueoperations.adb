package body QueueOperations
is

   procedure ReverseQueue(Q : in out Queues.Queue)
   is
      S: Stacks.Stack;
      X: Integer;
   begin
      Stacks.ClearStack(S);
      while not Queues.EmptyQueue(Q) loop
         Queues.DeQueue(Q, X);
         Stacks.Push(S, X);
      end loop;
      while not Stacks.EmptyStack(S) loop
         Stacks.Pop(S, X);
         Queues.EnQueue(Q, X);
      end loop;
   end ReverseQueue;

end QueueOperations;
