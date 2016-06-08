package Logger with SPARK_Mode
is

   protected type Msg_Queue_T is
      entry E;
   private
      Num_Queued : Natural := 0;
      Not_Empty  : Boolean := false;
   end Msg_Queue_T;

end Logger;
