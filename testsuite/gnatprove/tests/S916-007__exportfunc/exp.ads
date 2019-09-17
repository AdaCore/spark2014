package Exp is

   type Arr is array (Integer range <>) of Integer;

   function F (X : Arr) return Integer;
   pragma Export_Function (Internal => F, Mechanism => (X => Reference));

   procedure P (X : Arr);
   pragma Export_Procedure (Internal => P, Mechanism => (X => Reference));

end Exp;
