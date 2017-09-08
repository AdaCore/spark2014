package Mailbox_Proved
  with SPARK_Mode
is
   protected type Mailbox is
      entry Publish;
      entry Retrieve;
   private
      Num_Messages : Natural := 0;
   end Mailbox;

end Mailbox_Proved;
