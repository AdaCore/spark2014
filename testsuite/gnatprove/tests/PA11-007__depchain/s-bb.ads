package System.BB is

   subtype Interrupt_ID is Natural range 0 .. 20;

   type Interrupt_Handler is access procedure (Id : Interrupt_ID);

   procedure Attach_Handler
     (Handler : not null Interrupt_Handler;
      Prio    : Interrupt_Priority);

end System.BB;
