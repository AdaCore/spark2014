package body Bar is

   subtype R is Real'Base;

   function Im (X : Complex) return Real'Base is
   begin
      return X.Im;
   end Im;

   function Im (X : Imaginary) return Real'Base is
   begin
      return R (X);
   end Im;

end Bar;
