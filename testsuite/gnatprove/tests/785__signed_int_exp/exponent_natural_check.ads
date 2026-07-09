package Exponent_Natural_Check
  with SPARK_Mode
is

   --  The predefined "**" operator for a signed integer type requires the
   --  right operand to be of type Natural (RM 4.5.6). When the exponent
   --  originates as a general Integer, converting it to Natural carries a
   --  range check that provers must discharge.

   subtype Small_Base is Integer range -2 .. 2;

   function Safe_Power (Base : Small_Base; Exp : Integer) return Integer
   with
     Pre  => Exp >= 0 and then Exp <= 30,
     Post => Safe_Power'Result = Base ** Natural (Exp);

end Exponent_Natural_Check;
