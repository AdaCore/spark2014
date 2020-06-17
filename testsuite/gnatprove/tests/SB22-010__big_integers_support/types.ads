with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;

package Types with
  SPARK_Mode
is

   Zero : constant Big_Integer := To_Big_Integer (0);
   function "+" (R : Integer) return Big_Integer renames To_Big_Integer;
   type Extended_Index_Type is new Integer range - 1 .. 9;
   subtype Index_Type is Extended_Index_Type range 0 .. 9;

   type Integer_Curve25519 is array (Index_Type range <>) of Integer;
   subtype Integer_255 is Integer_Curve25519 (Index_Type);

   type Big_Ints is array (Index_Type) of Big_Integer;

   function Two_Power (Expon : Natural) return Big_Integer is
      (2 ** Expon);
   Conversion_Array : constant Big_Ints := (Two_Power (0),   Two_Power (26),
                                            Two_Power (51),  Two_Power (77),
                                            Two_Power (102), Two_Power (128),
                                            Two_Power (153), Two_Power (179),
                                            Two_Power (204), Two_Power (230));
end Types;
