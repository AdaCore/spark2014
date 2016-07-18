package Aida is
   pragma Pure;

   -- max  2147483647
   -- min -2147483648
   type Integer_Type is range -2**31 .. (2**31 - 1);
   for Integer_Type'Size use 32;

   type Long_Integer_Type is range -2**63 .. (2**63 - 1);
   for Long_Integer_Type'Size use 64;

end Aida;
