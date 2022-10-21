with SPARK.Containers.Formal.Ordered_Maps;
with SPARK.Containers.Formal.Unbounded_Ordered_Maps;

with Types;  use Types;
with Axioms; use Axioms;

package Test_OMaps with SPARK_Mode is
   package OMaps is new SPARK.Containers.Formal.Ordered_Maps
     (Key_Type     => T,
      Element_Type => T);
   package Ax_OMaps is new SPARK.Containers.Formal.Ordered_Maps
     (Key_Type       => T,
      Element_Type   => T,
      Eq_Reflexive   => Axiom_Eq_Reflexive,
      Eq_Symmetric   => Axiom_Eq_Symmetric,
      Eq_Transitive  => Axiom_Eq_Transitive,
      Lt_Irreflexive => Lemma_Lt_Irreflexive,
      Lt_Asymmetric  => Axiom_Lt_Asymmetric,
      Lt_Transitive  => Axiom_Lt_Transitive,
      Lt_Order       => Axiom_Lt_Order);
   package U_OMaps is new SPARK.Containers.Formal.Unbounded_Ordered_Maps
     (Key_Type     => T,
      Element_Type => T);
   package Ax_U_OMaps is new SPARK.Containers.Formal.Unbounded_Ordered_Maps
     (Key_Type       => T,
      Element_Type   => T,
      Eq_Reflexive   => Axiom_Eq_Reflexive,
      Eq_Symmetric   => Axiom_Eq_Symmetric,
      Eq_Transitive  => Axiom_Eq_Transitive,
      Lt_Irreflexive => Lemma_Lt_Irreflexive,
      Lt_Asymmetric  => Axiom_Lt_Asymmetric,
      Lt_Transitive  => Axiom_Lt_Transitive,
      Lt_Order       => Axiom_Lt_Order);
end Test_OMaps;
