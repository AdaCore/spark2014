with Ada.Interrupts.Names; with P;

package Interrupt_Handler_With_Current_Task with SPARK_Mode is

   pragma Unreserve_All_Interrupts;

   protected type PT is
      entry Wait_For_SIGINT;
   private
      procedure Handle;
      --  pragma Interrupt_Handler (Handle);
      pragma Attach_Handler (Handle, P.Bad_Interrupt_ID_Ptr.all); --Ada.Interrupts.Names.SIGINT);
      Received : Boolean := False;
   end;

   task Reporter;

end;
