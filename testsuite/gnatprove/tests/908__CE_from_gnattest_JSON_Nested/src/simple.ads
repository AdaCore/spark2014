package Simple
with SPARK_Mode
is

   type T is range 0 .. 10;

   function Nested_CE (X, Y : T) return T
     with Pre => X + Y <= 10 and X + Y >= 5;

end Simple;
