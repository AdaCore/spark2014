package body Twodim is 

   function F (M : Matrix; I : One_Ten; K : One_Twenty) return Integer
   is
   begin
      --  Neither the division by zero, nor the overflow check, nor the access
      --  check should be proved correct
      return 1 / (M (I,K+1) + 1);
   end F;

   function G (M : Any_Matrix) return Integer is
   begin
      return M'Length (1) + M'Length (2);
   end G;

end Twodim;
