package body Forall
is
   function Get_Zero (X : A) return Integer
   is
   begin
      return X (1);
   end Get_Zero;

   function Has_Zero (X : A) return Integer
   is
   begin
      return X (1);
   end Has_Zero;

end Forall;
