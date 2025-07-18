package body Simple
with SPARK_Mode
is

   function Nested_CE (X, Y : T) return T is
      Z : T;
   begin
      Z := X + Y - 5;
      return Z / Z;
   end Nested_CE;

end Simple;
