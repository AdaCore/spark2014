with System;

package Common is

   function Bad_Priority           return Integer is (System.Priority'Last + 1);
   function Bad_Interrupt_Priority return Integer is (System.Interrupt_Priority'Last + 1);

end;
