with System;

package P is

   protected type PT is
      pragma Interrupt_Priority (System.Priority'Last - 1);
      procedure Proc;
   end;

   task type TT is
      pragma Interrupt_Priority (System.Priority'Last - 2);
   end;

   PO : PT;
   TO : TT;

end;
