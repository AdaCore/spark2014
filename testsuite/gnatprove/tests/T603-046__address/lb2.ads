with System;

package LB2
with
   SPARK_Mode
is
   type X (<>) is limited private;

private
   type A is limited record
      E : Integer;
   end record
   with
      Volatile, Async_Readers, Object_Size => 32;

   type X is limited new A;

   I : X
   with
      Volatile,
      Async_Readers,
      Address => System'To_Address (16#1234_5678#);

end LB2;
