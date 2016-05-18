generic
   Version : Integer;
package Lemmas
  with SPARK_Mode
is
   subtype Int is Integer;
   subtype Nat is Int range 0 .. Int'Last;
   subtype Pos is Int range 1 .. Int'Last;

   procedure Lemma_Div_Is_Monotonic1
     (Val1  : Int;
      Val2  : Int;
      Denom : Pos)
   with
     Global => null,
     Pre  => Val1 <= Val2,
     Post => Val1 / Denom <= Val2 / Denom;

   procedure Lemma_Div_Is_Monotonic2
     (Val1  : Int;
      Val2  : Int;
      Denom : Pos)
   with
     Global => null,
     Pre  => Val1 <= Val2,
     Post => Val1 / Denom <= Val2 / Denom;

end Lemmas;
