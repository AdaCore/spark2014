package body Communications is

   protected body Mailbox is

      function Item_Count return Message_Count is (Count);

      procedure Install_Message (N : in Integer) is
      begin
         -- Ignore messages if there is no space for them!
         if Count < Maximum_Message_Count then
            Messages(Next_In) := N;
            Next_In := Next_In + 1;
            Count := Count + 1;
         end if;
      end Install_Message;

      entry Get_Message (N : out Integer) when Count > 0 is
      begin
         N := Messages(Next_Out);
         Next_Out := Next_Out + 1;
         Count := Count - 1;
      end Get_Message;

   end Mailbox;

   task body Process is
      Val : Integer;
   begin
      loop
         Mailbox.Install_Message (42);
         Mailbox.Get_Message (Val);
      end loop;
   end Process;

end Communications;
