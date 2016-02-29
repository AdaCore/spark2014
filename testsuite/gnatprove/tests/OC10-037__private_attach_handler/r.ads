with System;

package R with SPARK_Mode is

   protected type PT (X : Integer; Y : Integer; Z : Integer) is
      procedure Dummy;
   private
      pragma SPARK_Mode (Off);
      pragma Attach_Handler (Dummy, 10);
      pragma Interrupt_Priority (System.Any_Priority'Last);
   end;

   PO : PT (X => 1, Y => 2, Z => 3);

end;
