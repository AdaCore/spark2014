package body Mailbox_Init
  with SPARK_Mode
is
   Max : constant := 100;

   protected body Mailbox is
      entry Publish when Not_Full is
      begin
         Num_Messages := Num_Messages + 1;
         Not_Empty := True;
         if Num_Messages = Max then
            Not_Full := False;
         end if;
      end Publish;

      entry Retrieve when Not_Empty is
      begin
         Num_Messages := Num_Messages - 1;
         Not_Full := True;
         if Num_Messages = 0 then
            Not_Empty := False;
         end if;
      end Retrieve;
   end Mailbox;

end Mailbox_Init;
