package Sgs is

   type Float is digits 6;

   function C (X : Integer) return Float is (Float (X));

   subtype T is Integer range 0 .. 14;
   subtype U is Float range 0.0 .. 14.0;

   procedure F (X1 : T; X2 : T; X3 : T; X4 : T);

   function A (X: T) return Float
   with Post => A'Result >= 0.0 and then A'Result <= 14.0;

end Sgs;
