with Interfaces;

package Aida.Int32 with SPARK_Mode is

   -- max  2147483647
   -- min -2147483648
   type T is range -2**31 .. (2**31 - 1);
   for T'Size use 32;

   function ">=" (L, R : T) return Boolean;

   function "<=" (L, R : T) return Boolean;

private

   use type Interfaces.Integer_32;

   function ">=" (L, R : T) return Boolean is (Interfaces.Integer_32 (L) >= Interfaces.Integer_32 (R));

   function "<=" (L, R : T) return Boolean is (Interfaces.Integer_32 (L) <= Interfaces.Integer_32 (R));

end Aida.Int32;
