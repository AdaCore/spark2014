with System;
with Interrupt_Priority;
use Interrupt_Priority;
package Bad with SPARK_Mode is
   function Too_Big return Integer is (System.Any_Priority'Last + 1);
   P1 : No_Interrupt_Needed_1 (Too_Big);           --@RANGE_CHECK:FAIL
end Bad;
