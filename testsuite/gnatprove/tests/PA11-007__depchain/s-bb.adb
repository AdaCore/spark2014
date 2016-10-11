with System.BB.Board_Support;

package body System.BB is

   procedure Interrupt_Wrapper (Vector : Integer);

   procedure Attach_Handler
     (Handler : not null Interrupt_Handler;
      Prio    : Interrupt_Priority)
   is
   begin
      Board_Support.Install_Interrupt_Handler
        (Interrupt_Wrapper'Address, Prio);
   end Attach_Handler;

   procedure Interrupt_Wrapper (Vector : Integer) is
   begin
      null;
   end Interrupt_Wrapper;

end System.BB;
