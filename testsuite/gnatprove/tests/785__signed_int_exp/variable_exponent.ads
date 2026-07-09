package Variable_Exponent
  with SPARK_Mode
is

   --  Exponentiation where the exponent (and possibly the base) is a
   --  run-time value rather than a literal. Overflow freedom then depends
   --  on a nonlinear relationship between Base and Exp, which is much
   --  harder for automatic provers than the literal-exponent case.

   subtype Small_Base is Integer range -2 .. 2;
   subtype Bounded_Exp is Natural range 0 .. 30;

   function Power (Base : Small_Base; Exp : Bounded_Exp) return Integer
   with Post => Power'Result = Base ** Exp;

   subtype Tiny_Base is Integer range -10 .. 10;
   subtype Tiny_Exp is Natural range 0 .. 8;

   function Small_Power (Base : Tiny_Base; Exp : Tiny_Exp) return Integer
   with Post => Small_Power'Result = Base ** Exp;

   --  General law of exponents: relates two calls to "**" with the same
   --  base and different exponents to a single call with the summed
   --  exponent. True for all non-negative exponents, but proving it in
   --  general requires induction, which the built-in provers do not
   --  perform automatically.
   function Product_Of_Powers
     (Base : Integer; Exp_1, Exp_2 : Natural) return Boolean
   with
     Pre  => Base in -2 .. 2 and then Exp_1 <= 15 and then Exp_2 <= 15,
     Post => Product_Of_Powers'Result;

end Variable_Exponent;
