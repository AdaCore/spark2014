with Ada.Numerics.Big_Numbers.Big_Integers; use Ada.Numerics.Big_Numbers.Big_Integers;

package Test with
   SPARK_Mode,
   Ghost
is

   procedure Foo (Value : Big_Integer) with
     Pre  => 0 <= Value,
     Ghost;

   procedure Foo_3 (Value : Big_Integer) with
     Pre  => 10_000_000_000_000_000_000_000_000_000 = Value,
     Ghost;

   procedure Foo_4 (Value : Big_Integer) with
     Pre  => From_String ("0") <= Value,
     Ghost;

end Test;
