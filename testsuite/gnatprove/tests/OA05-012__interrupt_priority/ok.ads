with System;
with Interrupt_Priority;
use Interrupt_Priority;
package Ok with SPARK_Mode is
   P1 : No_Interrupt_Needed_1 (System.Any_Priority'First);
   P2 : No_Interrupt_Needed_1 (System.Interrupt_Priority'First);
   P3 : No_Interrupt_Needed_2 (System.Any_Priority'First);
   P4 : No_Interrupt_Needed_2 (System.Interrupt_Priority'First);
   P5 : Interrupt_Needed_1 (System.Interrupt_Priority'First);
end OK;
