package System.BB.Board_Support is

   procedure Install_Interrupt_Handler
     (Handler : Address;
      Prio    : Interrupt_Priority);

end System.BB.Board_Support;
