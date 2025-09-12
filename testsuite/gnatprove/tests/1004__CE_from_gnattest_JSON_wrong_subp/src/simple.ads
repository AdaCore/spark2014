package Simple
with SPARK_Mode
is

   type T is range 0 .. 10;

   function Foo (X, Y : T) return T
     with Post => Foo'Result < 15;

end Simple;
