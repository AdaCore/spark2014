with System;

package P is

   protected type PT is
      pragma Interrupt_Priority (System.Interrupt_Priority'First);

      procedure Dummy;
   end;

   PO : PT;

end;
