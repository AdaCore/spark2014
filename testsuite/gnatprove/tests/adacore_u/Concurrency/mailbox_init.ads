package Mailbox_Init
  with SPARK_Mode
is
   protected type Mailbox is
      entry Publish;
      entry Retrieve;
   private
      Not_Empty    : Boolean := True;
      Not_Full     : Boolean := False;
      Num_Messages : Natural := 0;
   end Mailbox;

end Mailbox_Init;
