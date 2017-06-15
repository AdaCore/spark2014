-- Factorial computation

package Factorial
with SPARK_Mode
is

   function Mathematical_Factorial (X : Integer) return Integer is
     (if X <= 1 then 1 else X * Mathematical_Factorial (X-1))
   with Pre => X in 1 .. 12,
   Ghost;

   function Fact (X : Integer) return Integer
     with Pre => X in 1 .. 12,
     Post => Fact'Result = Mathematical_Factorial (X);

end Factorial;
