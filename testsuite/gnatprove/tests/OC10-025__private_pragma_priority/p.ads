package P is

   protected type PT is
   private
      procedure Dummy;
      pragma Attach_Handler (Dummy, 10);
      --pragma Interrupt_Priority (-1);
      pragma Priority (-1);
   end;

   PO : PT;

end;
