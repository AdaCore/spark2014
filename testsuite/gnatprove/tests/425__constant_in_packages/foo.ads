package Foo with SPARK_Mode is
   function Id (X : Integer) return Integer is (X);
   subtype Small_Int is Integer range 1 .. 10;
   C : constant Small_Int := Id (11); --@RANGE_CHECK:FAIL

   procedure P;
end Foo;
