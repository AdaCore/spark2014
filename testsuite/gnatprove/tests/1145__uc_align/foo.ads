with System;

package Foo
with SPARK_Mode => On
is
   type T is tagged private;
   procedure Foo (Self : T);
private
   type T is tagged record
      Address : System.Address;
   end record;
end Foo;
