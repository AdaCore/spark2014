with System;

package body Pkg2
with
   SPARK_Mode,
   Refined_State => (State => Descriptors)
is
   Descriptors : Integer
   with
      Address => System'To_Address (16#1234_5678#);

   pragma Annotate (GNATprove, Intentional, "initialization of", "Only suppressing continuation line");

   procedure Foo
   is
   begin
      Descriptors := 0;
   end Foo;

end Pkg2;
