-- Factorial computation

package Factorial
with SPARK_Mode
is

   function Mathematical_Factorial (X : Integer) return Integer is
     (if X = 1 then 1
      elsif X = 12 then X * Mathematical_Factorial (11)
      else X * Mathematical_Factorial (X-1))
   with
     Ghost,
     Subprogram_Variant => (Decreases => X),
     Pre => X in 1 .. 12;

   function Fact (X : Integer) return Integer
   with
     Pre  => X in 1 .. 12,
     Post => Fact'Result = Mathematical_Factorial (X);

end Factorial;
