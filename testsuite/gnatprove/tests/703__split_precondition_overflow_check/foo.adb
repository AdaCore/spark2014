with Ada.Numerics.Generic_Elementary_Functions;
with Ada.Numerics.Long_Elementary_Functions;
use Ada.Numerics.Long_Elementary_Functions;

procedure Foo (X : Long_Float; Y : Long_Float; Z : Long_Float)
  with SPARK_Mode
is
   R : Long_Float;
begin
   R := Log (X);
   R := X ** Y;
   R := Log (X, Y);
   R := Exp (X);
   R := Tan (X);
   R := Tan (X, Y);
   R := Cot (X);
   R := Cot (X, Y);
   R := Cosh (X);
   R := Sinh (X);
   R := Coth (X);
   R := Arcsinh (X);
   R := Arccosh (X);
end Foo;
