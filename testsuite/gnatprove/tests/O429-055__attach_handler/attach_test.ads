package Attach_Test is

   protected type Prot is
      procedure Start
         with Attach_Handler => 1; --@INTERRUPT_RESERVED:FAIL
      procedure Stop
         with Attach_Handler => 2; --@INTERRUPT_RESERVED:FAIL
   private
      A : Integer := 0;
   end Prot;

   X : Prot;
end Attach_Test;
