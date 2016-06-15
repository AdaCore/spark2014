pragma Profile(Ravenscar);
pragma Partition_Elaboration_Policy(Sequential);
pragma SPARK_Mode(On);

package body Core is

   protected body Mailbox is

      function Item_Count return Message_Count is (Count);


      procedure Install_Message(N : in Integer) is
      begin
         -- Ignore messages if there is no space for them!
         if Count < Maximum_Message_Count then
            Messages(Next_In).Value := N;
            Messages(Next_In).Size := 0;
            Next_In := Next_In + 1;
            Count := Count + 1;
            Message_Waiting := True;
         end if;
      end Install_Message;


      entry Get_Message(N : out Integer) when Message_Waiting is
      begin
         pragma Assert (Message_Waiting); --@ASSERT:PASS
         N := Messages(Next_Out).Value;
         Next_Out := Next_Out + 1;
         Count := Count - 1;
         Message_Waiting := (Count > 0);
      end Get_Message;

   end Mailbox;

end Core;
