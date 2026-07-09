package body Exponent_Natural_Check
  with SPARK_Mode
is

   function Safe_Power (Base : Small_Base; Exp : Integer) return Integer is
   begin
      return Base ** Natural (Exp);
   end Safe_Power;

end Exponent_Natural_Check;
