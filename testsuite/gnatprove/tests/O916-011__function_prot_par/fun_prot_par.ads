package Fun_Prot_Par is
   protected type Prot is
      function Get_A return Integer;
   private
      A : Integer := 0;
   end Prot;

   function F (X : Prot) return Integer;
end Fun_Prot_Par;
