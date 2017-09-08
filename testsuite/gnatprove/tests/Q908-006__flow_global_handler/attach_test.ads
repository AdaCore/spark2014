package Attach_Test is

   Uninit : Integer;

   protected type Prot is
      procedure Intr
         with Attach_Handler => 1;
   private
      A : Integer := 0;
   end Prot;

   X : Prot;

end Attach_Test;
