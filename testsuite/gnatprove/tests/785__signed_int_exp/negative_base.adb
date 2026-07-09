package body Negative_Base
  with SPARK_Mode
is

   function Neg_Square_Equals_Square (X : Small) return Boolean is
   begin
      return (-X) ** 2 = X ** 2;
   end Neg_Square_Equals_Square;

   function Neg_Cube_Is_Minus_Cube (X : Small) return Boolean is
   begin
      return (-X) ** 3 = -(X ** 3);
   end Neg_Cube_Is_Minus_Cube;

   function Neg_Power_Sign (X : Tiny; N : Natural) return Boolean is
   begin
      return
        (if N mod 2 = 0 then (-X) ** N = X ** N else (-X) ** N = -(X ** N));
   end Neg_Power_Sign;

end Negative_Base;
