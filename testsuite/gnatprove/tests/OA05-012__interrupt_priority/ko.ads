with System;
with Interrupt_Priority;
use Interrupt_Priority;
package KO with SPARK_Mode is
  P :  Interrupt_Needed_1 (System.Any_Priority'First);
end KO;
