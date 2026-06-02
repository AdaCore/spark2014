package body Simple
with SPARK_Mode
is

   function Foo (X, Y : T) return T is
   begin
      return X + Y;
   end Foo;

end Simple;
