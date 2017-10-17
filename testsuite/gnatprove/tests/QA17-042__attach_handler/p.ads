with Ada.Interrupts;

package P is

   use type Ada.Interrupts.Interrupt_Id;

   function Zero return Integer is (0);

   protected PO is
      procedure Irq with Attach_Handler => 1 / Ada.Interrupts.Interrupt_Id (Zero);
   end;

end;
