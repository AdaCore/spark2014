package body Logger with SPARK_Mode
is

   protected body Msg_Queue_T is
      entry E when Not_Empty is
      begin
         pragma Assert (Num_Queued > 0);
      end E;
   end Msg_Queue_T;

end Logger;
