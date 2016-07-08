with System;

package body Pkg
with
   SPARK_Mode,
   Refined_State => (State => Descriptors)
is
   Descriptors : Integer
   with
      Address => System'To_Address (16#1234_5678#);

   pragma Annotate (GNATprove, Intentional, "not initialized", "Suppressing main message should suppress cont line, too");

   procedure Foo
   is
   begin
      Descriptors := 0;
   end Foo;

end Pkg;
