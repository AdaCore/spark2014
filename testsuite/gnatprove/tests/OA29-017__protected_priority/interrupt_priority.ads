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
end Interrupt_Priority;
