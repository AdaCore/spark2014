package body Forall
is
   function Get_One (X : A) return Integer
   is
   begin
      return X (1);
   end Get_One;
end Forall;
