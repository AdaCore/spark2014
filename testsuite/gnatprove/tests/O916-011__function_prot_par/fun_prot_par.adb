package body Fun_Prot_Par is
   protected body Prot is
      function Get_A return Integer is
      begin
         return A;
      end Get_A;
   end Prot;

   function F (X : Prot) return Integer is
   begin
      return X.Get_A;
   end F;

end Fun_Prot_Par;
