with Ada.Numerics.Big_Numbers.Big_Integers;
use Ada.Numerics.Big_Numbers.Big_Integers;

package Fast_Exponentiation is

   subtype Int is Big_Integer;

   function Fast_Exp (X : Int; N : Natural) return Int
   with
     Subprogram_Variant => (Decreases => N),
     Post => Fast_Exp'Result = X ** N;

   function Fast_Exp_Imperative (X : Int; N : Natural) return Int
   with
     Post => Fast_Exp_Imperative'Result = X ** N;


end Fast_Exponentiation;
