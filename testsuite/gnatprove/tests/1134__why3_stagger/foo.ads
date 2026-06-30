package Foo
  with SPARK_Mode
is
   function Double (X : Natural) return Natural
   with Pre => X <= Natural'Last / 2, Post => Double'Result = 2 * X;
end Foo;
