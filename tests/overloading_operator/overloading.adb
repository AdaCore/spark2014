package body Overloading
is

   function "+"(X,Y : Complex) return Complex
   is
   begin
      return (X.Re + Y.Re, X.Im + Y.Im);
   end "+";

   procedure Overload
     (J, K : in Integer; I : out Integer;
      B, C : in Complex; A : out Complex)
   is
   begin
      I := J + K;
      A := B + C;
   end Overload;

end Overloading;
