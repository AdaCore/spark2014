package body Twodim is

   function F (M : Matrix; I : One_Ten; K : One_Twenty) return Integer
   is
   begin


      return 1 / (M (I,K+1) + 1); -- @DIVISION_CHECK:FAIL @OVERFLOW_CHECK:FAIL @INDEX_CHECK:FAIL
   end F;

   function G (M : Any_Matrix) return Integer is
   begin
      return M'Length (1) + M'Length (2);
   end G;

end Twodim;
