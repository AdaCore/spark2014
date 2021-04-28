package Lemma with SPARK_Mode is

   procedure Prove_Conversion (X : Integer) with
     Global => null,
     Pre    => X > 0,
     Post   => Float (X) >= 1.0;
end Lemma;
