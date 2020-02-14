with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;
with Types; use Types;
with Conversion; use Conversion;

package Curve25519 with
  SPARK_Mode
is

   Min_Add : constant Integer := -2**30 + 1;
   Max_Add : constant Integer := 2**30 - 1;

   function Add (X, Y : Integer_255) return Integer_255 with
     Pre  => (for all J in X'Range =>
                X (J) in Min_Add .. Max_Add
                and then Y (J) in Min_Add .. Max_Add),
     Post => ((for all J in X'Range =>
                Add'Result (J) = X (J) + Y (J)))
                and then To_Integer_255 (Add'Result) =
                            To_Integer_255 (X) + To_Integer_255 (Y);

end Curve25519;
