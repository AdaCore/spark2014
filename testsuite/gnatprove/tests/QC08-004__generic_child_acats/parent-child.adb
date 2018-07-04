package body Parent.Child is

   function "+" (Left, Right : Complex_Type)
     return Complex_Type is

   begin
      return ( (Left.Real + Right.Real, Left.Imag + Right.Imag) );
   end "+";

   function "-" (Right : Complex_Type) return Complex_Type is
   begin
      return (-Right.Real, -Right.Imag);
   end "-";

end Parent.Child;
