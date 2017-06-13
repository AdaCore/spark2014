package body Tasking is

   protected body Mailbox is
      procedure Send_Message(M : in Message_Type) is
      begin
         -- Ignore messages if the mailbox is full.
         if Count < Message_Array'Length then
            Message_Array(Next_In) := M;
            Count := Count + 1;
            Non_Empty := True;

            if Next_In = Message_Index_Type'Last then
               Next_In := Message_Index_Type'First;
            else
               Next_In := Next_In + 1;
            end if;
         end if;
      end Send_Message;


      entry Get_Message(M : out Message_Type) when Non_Empty is
      begin
         M := Message_Array(Next_Out);
         Count := Count - 1;
         if Count = 0 then
            Non_Empty := False;
         end if;

         if Next_Out = Message_Index_Type'Last then
            Next_Out := Message_Index_Type'First;
         else
            Next_Out := Next_Out + 1;
         end if;
      end Get_Message;
   end Mailbox;

end Tasking;
