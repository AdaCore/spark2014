pragma Ravenscar;
pragma Partition_Elaboration_Policy (Sequential);
with System; use System;

package Interrupt_Priority with SPARK_Mode is
   protected type No_Interrupt_Needed_1 (C : Any_Priority) is
      pragma Priority (C);
      procedure OK;
   private
      I : Integer := 0;
   end No_Interrupt_Needed_1;
   protected type Interrupt_Needed_1 (C : Any_Priority) is
      pragma Priority (C);
      procedure OK with Attach_Handler => 1;
   private
     I : Integer := 0;
   end Interrupt_Needed_1;
   protected type No_Interrupt_Needed_2 (C : Any_Priority) is
      pragma Priority (C);
      procedure OK with Interrupt_Handler => False;
   private
      I : Integer := 0;
   end No_Interrupt_Needed_2;
end Interrupt_Priority;
