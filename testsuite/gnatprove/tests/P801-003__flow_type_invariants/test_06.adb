package body Test_06 is

   function F (X : T) return Boolean
   is
   begin
      return X.A or else X.B;
   end F;

end Test_06;
