with Ada.Numerics.Big_Numbers.Big_Integers;
use Ada.Numerics.Big_Numbers.Big_Integers;

package body Nouse is

   procedure Lemma_Lower_Mult (A, B, C : Big_Natural)
   with
     Ghost,
     Pre  => A <= B,
     Post => A * C <= B * C;

   procedure Lemma_Lower_Mult (A, B, C : Big_Natural) is null;

   procedure P is null;

end Nouse;
