package body Test with SPARK_Mode is

   procedure Enable_Interrupt
   is
   begin
      IO_BANK_Periph.INTR (0) := 0;
   end Enable_Interrupt;

end Test;
