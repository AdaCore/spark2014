pragma Profile (Jorvik);
pragma Partition_Elaboration_Policy (Sequential);
with System;
with Ada.Interrupts;

package Ext with SPARK_Mode is

   --  Check that range and definitions of constants with variable inputs
   --  referenced in protected objects are available for proof.

   X : System.Priority;
   D : constant System.Priority := X;
   C : constant System.Any_Priority := D;

   protected type PT1 is
      pragma Priority (C); -- @RANGE_CHECK:PASS
   end;

   protected type PT2 is
   private
      X : System.Priority := C; -- @RANGE_CHECK:PASS
   end;

   function To_Interrupt (X : System.Priority) return Ada.Interrupts.Interrupt_ID
     with Global => null,
     Import;

   protected type PT3 is
      procedure Proc with Attach_Handler => To_Interrupt (C); -- @RANGE_CHECK:PASS
   private
   end;

   --  Same as above, but with an abstract state. Only test interrupt
   --  handlers as variable inputs are not allowed in initial value of private
   --  components and in pragma priority.

   package P is
      function To_Prio return System.Priority;
   private
      pragma SPARK_Mode (Off);
      X : System.Priority;
      function To_Prio return System.Priority is (X);
   end P;
   use P;

   protected type PT6 is
      procedure Proc with Attach_Handler => To_Interrupt (To_Prio);
   private
   end;
end Ext;
