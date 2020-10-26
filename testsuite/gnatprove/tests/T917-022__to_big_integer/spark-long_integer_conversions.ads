pragma SPARK_Mode;

with Ada.Numerics.Big_Numbers.Big_Integers;
use Ada.Numerics.Big_Numbers.Big_Integers;

package SPARK.Long_Integer_Conversions is new
  Signed_Conversions (Long_Integer);
