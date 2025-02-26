package Oneliner with SPARK_Mode is

   type T is range 0 .. 10;

   function Foo (X : T) return T is (X * X);

end Oneliner;
