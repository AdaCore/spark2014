package body Axioms with SPARK_Mode is

   procedure Lemma_Equivalent_Reflexive (X : T) is
   begin
      Axiom_Eq_Reflexive (X);
      Axiom_Equivalent_Reflexive (X, X);
   end Lemma_Equivalent_Reflexive;

   procedure Lemma_Lt_Irreflexive (X : T) is
   begin
      Axiom_Eq_Reflexive (X);
      Axiom_Lt_Irreflexive (X, X);
   end Lemma_Lt_Irreflexive;

end Axioms;
