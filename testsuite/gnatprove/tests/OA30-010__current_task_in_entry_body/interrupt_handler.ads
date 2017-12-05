with Ada.Interrupts;          use Ada.Interrupts;
with Ada.Task_Identification; use Ada.Task_Identification;

package Interrupt_Handler
is

   Interrupt : aliased Ada.Interrupts.Interrupt_ID;

   protected type PO is
      pragma Spark_Mode (On);
      procedure P;
      pragma Attach_Handler (P, Interrupt);
   private
      T : Task_Id := Null_Task_Id;
   end;
end Interrupt_Handler;
