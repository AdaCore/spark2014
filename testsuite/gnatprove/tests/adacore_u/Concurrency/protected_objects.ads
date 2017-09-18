with Ada.Interrupts.Names; use Ada.Interrupts.Names;
with System;

package Protected_Objects
  with SPARK_Mode
is
   protected P1 with
     Interrupt_Priority => System.Interrupt_Priority'First
   is
      procedure Set (V : Natural);
      function Get return Natural;
      entry Reset;
      procedure Signal with Attach_Handler => SIGINT;
   private
      The_Data : Natural := 0;
   end P1;

   protected type PT with
     Interrupt_Priority => System.Interrupt_Priority'First
   is
      procedure Set (V : Natural);
      function Get return Natural;
      entry Reset;
      procedure Signal with Attach_Handler => SIGINT;
   private
      The_Data : Natural := 0;
   end PT;
   P2 : PT;

   type PA is array (1 .. 3) of PT;
   P3 : PA;

   type PR is record
      A, B : PT;
   end record with Volatile;
   P4 : PR;

end Protected_Objects;
