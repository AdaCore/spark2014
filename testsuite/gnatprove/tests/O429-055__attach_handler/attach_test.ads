package Attach_Test is

   protected type Prot is
      procedure Start
         with Attach_Handler => 1;
      procedure Stop
         with Attach_Handler => 2;
   private
      A : Integer := 0;
   end Prot;

   X : Prot;
end Attach_Test;
