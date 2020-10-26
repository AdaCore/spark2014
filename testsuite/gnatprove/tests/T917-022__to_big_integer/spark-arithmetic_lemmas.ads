with Ada.Numerics.Big_Numbers.Big_Integers;
use Ada.Numerics.Big_Numbers.Big_Integers;

generic
   type Int is range <>;
   with function Big (V : Int) return Big_Integer is <>;
package SPARK.Arithmetic_Lemmas
  with SPARK_Mode,
       Ghost
is
   subtype Nat is Int range 0 .. Int'Last;

   procedure Lemma_Mult_Is_Monotonic
     (Val1   : Int;
      Val2   : Int;
      Factor : Nat)
   with
     Global => null,
     Pre  => Val1 <= Val2,
     Post => Big (Val1) * Big (Factor) <= Big (Val2) * Big (Factor);

end SPARK.Arithmetic_Lemmas;
