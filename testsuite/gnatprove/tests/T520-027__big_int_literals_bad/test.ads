with Ada.Numerics.Big_Numbers.Big_Integers; use Ada.Numerics.Big_Numbers.Big_Integers;

package Test with
   SPARK_Mode,
   Ghost
is

   procedure Foo_2 (Value : Big_Integer) with
     Pre  => 10000000000000000000000000000000000000000000000000 <= Value,--@PRECONDITION:FAIL
     Ghost;

   Zero : String := "0";

   procedure Foo_5 (Value : Big_Integer) with
     Pre  => From_String (Zero) = Value,--@PRECONDITION:FAIL
     Ghost;

end Test;
