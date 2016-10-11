package body System.BB.Board_Support is
   First_IRQ : constant Interrupt_Priority := 2;

   procedure Install_Interrupt_Handler
     (Handler : Address;
      Prio    : Interrupt_Priority)
   is
   begin
       pragma Assert (Prio >= First_IRQ);
   end Install_Interrupt_Handler;


end System.BB.Board_Support;
