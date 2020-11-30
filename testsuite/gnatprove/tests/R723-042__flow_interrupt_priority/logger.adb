package body Logger
is
   -- protected type to implement the buffer
   protected type Msg_Queue_T is
      procedure New_Msg;
      pragma Attach_Handler (New_Msg, 10);
   end Msg_Queue_T;

   queue : Msg_Queue_T;

   -- implementation of the message queue
   protected body Msg_Queue_T is
      procedure New_Msg is null;
   end Msg_Queue_T;

   procedure log is
   begin
      queue.New_Msg;
   end log;

end Logger;
