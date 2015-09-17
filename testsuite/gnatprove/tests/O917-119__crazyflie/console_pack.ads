with CRTP_Pack; use CRTP_Pack;
with Ada.Synchronous_Task_Control; use Ada.Synchronous_Task_Control;

package Console_Pack with SPARK_Mode is

   --  Procedures and functions

   --  Initialize the console module.
   procedure Console_Init;

   --  Flush the console buffer.
   procedure Console_Flush (Has_Succeed : out Boolean);

   --  Test if the console module is initialized.
   function  Console_Test return Boolean;

   --  Put a string in the console buffer, and send it if a newline
   --  character is found.
   procedure Console_Put_Line
     (Message     : String;
      Has_Succeed : out Boolean);

private

   --  Global variables

   Is_Init          : Boolean := False;
   Console_Access   : Suspension_Object;
   Message_To_Print : CRTP_Packet_Handler;

   --  Procedures and functions

   --  Send the console buffer via CRTP.
   procedure Console_Send_Message (Has_Succeed : out Boolean);

end Console_Pack;
