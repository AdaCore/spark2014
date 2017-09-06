package Volatile_Variable_Values
  with SPARK_Mode
is

   Nat : Natural with Volatile, Async_Writers;

   subtype Angle is Integer range 0 .. 360;
   Ang : Angle with Volatile, Async_Writers;

   subtype Subangle is Angle with Static_Predicate => Subangle in 0 .. 15 | 17 .. 42 | 43 .. 360;
   Sub : Subangle with Volatile, Async_Writers;

   procedure Check;

end Volatile_Variable_Values;
