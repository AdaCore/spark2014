with Bar;

package body Foo
with
   SPARK_Mode => On
is
   function Foobar return Natural
   is
      X : Natural := 0;
   begin
      X := 1;
      return X;
   end Foobar;
end Foo;
