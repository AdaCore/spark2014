package body Variable_Exponent
  with SPARK_Mode
is

   function Power (Base : Small_Base; Exp : Bounded_Exp) return Integer is
   begin
      return Base ** Exp;
   end Power;

   function Small_Power (Base : Tiny_Base; Exp : Tiny_Exp) return Integer is
   begin
      return Base ** Exp;
   end Small_Power;

   function Product_Of_Powers
     (Base : Integer; Exp_1, Exp_2 : Natural) return Boolean is
   begin
      return Base ** Exp_1 * Base ** Exp_2 = Base ** (Exp_1 + Exp_2);
   end Product_Of_Powers;

end Variable_Exponent;
