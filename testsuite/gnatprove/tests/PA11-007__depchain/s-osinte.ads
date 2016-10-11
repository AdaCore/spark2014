with System.BB;

package System.OS_Interface is

   subtype Interrupt_ID is System.BB.Interrupt_ID;

   subtype Interrupt_Handler is System.BB.Interrupt_Handler;

   procedure Attach_Handler
     (Handler : Interrupt_Handler;
      PO_Prio : Interrupt_Priority)
     renames System.BB.Attach_Handler;
   --  Attach a handler to a hardware interrupt

   Ticks_Per_Second : constant := 10;

   procedure Initialize_Timers;

end System.OS_Interface;
