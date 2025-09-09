with Ada.Interrupts.Names; use Ada.Interrupts.Names;
with System;               use System;

package Prots is

   protected type PO_T with Priority => 1 is
      procedure PP1;
   end;

   --  This protected object has just a signal handler, but no other protected
   --  operations. It is important to test this pattern separately since the
   --  phase1 handling (i.e., data stored in the ALI file) is different than if
   --  there would be also other protected operations. It is also important
   --  that there is *no explicit call* made to this operation.
   protected Signal_Handler
     with Interrupt_Priority => System.Interrupt_Priority'Last
   is
      procedure Teardown  --  @CEILING_PRIORITY_PROTOCOL:FAIL
      with Attach_Handler => SIGTERM;
   end Signal_Handler;

   --  The same as Signal_Handler, but defined as an explicit type + instance.
   protected type Signal2_Handler_Type
     with Interrupt_Priority => System.Interrupt_Priority'Last
   is
      procedure Teardown  --  @CEILING_PRIORITY_PROTOCOL:FAIL
      with Attach_Handler => SIGINT;
   end Signal2_Handler_Type;

   PO : PO_T;

   Signal2_Handler : Signal2_Handler_Type;

end Prots;
