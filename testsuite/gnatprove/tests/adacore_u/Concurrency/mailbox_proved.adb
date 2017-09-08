package body Mailbox_Proved
  with SPARK_Mode
is
   Max : constant := 100;

   protected body Mailbox is
      entry Publish when Num_Messages < Max is
      begin
         Num_Messages := Num_Messages + 1;
      end Publish;

      entry Retrieve when Num_Messages > 0 is
      begin
         Num_Messages := Num_Messages - 1;
      end Retrieve;
   end Mailbox;

end Mailbox_Proved;
