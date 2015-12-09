package P is

   protected type PT is
      pragma Interrupt_Priority;

      procedure Dummy;
   end;

   PO : PT;

end;
