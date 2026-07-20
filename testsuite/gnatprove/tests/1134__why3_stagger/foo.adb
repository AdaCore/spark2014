package body Foo
  with SPARK_Mode
is
   function Double (X : Natural) return Natural
   is (2 * X);
end Foo;
