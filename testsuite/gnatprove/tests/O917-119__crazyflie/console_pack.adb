package body Console_Pack with SPARK_Mode is

   procedure Console_Init is
   begin
      if Is_Init then
         return;
      end if;

      Set_True (Console_Access);
      Message_To_Print := CRTP_Create_Packet (CRTP_PORT_CONSOLE, 0);

      Is_Init := True;
   end Console_Init;

   function Console_Test return Boolean is
   begin
      return Is_Init;
   end Console_Test;

   procedure Console_Send_Message (Has_Succeed : out Boolean) is
   begin
      CRTP_Send_Packet
        (CRTP_Get_Packet_From_Handler (Message_To_Print), Has_Succeed);

      --  Reset the CRTP packet data contained in the handler
      CRTP_Reset_Handler (Message_To_Print);
   end Console_Send_Message;

   procedure Console_Flush (Has_Succeed : out Boolean) is
   begin
      Suspend_Until_True (Console_Access);
      Console_Send_Message (Has_Succeed);
      Set_True (Console_Access);
   end Console_Flush;

   procedure Console_Put_Line
     (Message     : String;
      Has_Succeed : out Boolean) is
      Free_Bytes_In_Packet : Boolean := True;
      procedure CRTP_Append_Character_Data is new CRTP_Append_Data (Character);
   begin
      for C of Message loop
         CRTP_Append_Character_Data
           (Message_To_Print, C, Free_Bytes_In_Packet);

         if not Free_Bytes_In_Packet then
            Console_Send_Message (Has_Succeed);
         end if;
      end loop;

      Console_Send_Message (Has_Succeed);
   end Console_Put_Line;

end Console_Pack;
