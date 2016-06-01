package body Logger
is
   type Log_Msg is null record;

   -- protected type to implement the buffer
   protected type Msg_Queue_T is
      procedure New_Msg (msg : in Log_Msg);
   end Msg_Queue_T;

   queue : Msg_Queue_T;

   -- implementation of the message queue
   protected body Msg_Queue_T is
      procedure New_Msg (msg : in Log_Msg) is null;
   end Msg_Queue_T;

   procedure log
   is
      msg : Log_Msg;
   begin
      queue.New_Msg(msg);
  null;
   end log;

end Logger;
