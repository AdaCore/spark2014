with Foo;
package Bar with SPARK_Mode is
   function Id (X : Integer) return Integer is (X);
   subtype Small_Int is Integer range 1 .. 10;
   C : constant Small_Int := Id (11);
   D : Integer := Foo.C;
end Bar;
