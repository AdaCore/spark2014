package Math_Euclid is

   function Divides (A, B : in Positive) return Boolean is (B mod A = 0) with Ghost;

   procedure Lemma_Divisor_Mod (A, B, X : Positive) with
     Ghost,
     Global => null,
     Pre  => Divides (X, A) and then Divides (X, B) and then not Divides (B, A),
     Post => Divides (X, A mod B);

end Math_Euclid;
