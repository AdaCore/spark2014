with Interrupt_Priority;
use Interrupt_Priority;
package Ok with SPARK_Mode is
   P1 : No_Interrupt_Needed_1 (1);
   P2 : No_Interrupt_Needed_1 (98);
   P3 : No_Interrupt_Needed_2 (1);
   P4 : No_Interrupt_Needed_2 (98);
   P5 : No_Interrupt_Needed_1 (98);
end OK;
