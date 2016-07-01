package body GNAT_Bug
is

   protected body Example_PT
   is

      procedure Test
      is
      begin
         null;
      end Test;

      procedure IRQ_Handler
      is
      begin
         null;
      end IRQ_Handler;

   end Example_PT;

end GNAT_Bug;
