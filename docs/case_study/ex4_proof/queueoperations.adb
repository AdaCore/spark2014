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
         pragma Loop_Invariant ((Queues.Size(Q) in 1 .. Queues.Max_Count) and
                                (Stacks.Size(S) = Count) and
                                (Count = Queues.Size(Q'Loop_Entry) - Queues.Size(Q)));
         Queues.DeQueue(Q, X);
         Stacks.Push(S, X);
         Count := Count + 1;
      end loop;
      while Count > 0 loop
         Stacks.Pop(S, X);
         Queues.EnQueue(Q, X);
         Count := Count - 1;
         pragma Loop_Invariant ((Stacks.Size(S) = Count) and
                                (Queues.Size(Q) >= 1) and
                                (Queues.Size(Q) = Count'Loop_Entry - Count));
      end loop;
   end ReverseQueue;

end QueueOperations;
