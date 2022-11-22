with SPARK.Containers.Formal.Hashed_Maps;
with SPARK.Containers.Formal.Unbounded_Hashed_Maps;

with Types;  use Types;
with Axioms; use Axioms;

package Test_HMaps with SPARK_Mode is
   package HMaps is new SPARK.Containers.Formal.Hashed_Maps
     (Key_Type        => T,
      Element_Type    => T,
      Equivalent_Keys => Equivalent,
      Hash            => Hash);
   package Ax_HMaps is new SPARK.Containers.Formal.Hashed_Maps
     (Key_Type                   => T,
      Element_Type               => T,
      Equivalent_Keys            => Equivalent,
      Hash                       => Hash,
      Eq_Reflexive               => Axiom_Eq_Reflexive,
      Eq_Symmetric               => Axiom_Eq_Symmetric,
      Eq_Transitive              => Axiom_Eq_Transitive,
      Equivalent_Keys_Reflexive  => Lemma_Equivalent_Reflexive,
      Equivalent_Keys_Symmetric  => Axiom_Equivalent_Symmetric,
      Equivalent_Keys_Transitive => Axiom_Equivalent_Transitive,
      Hash_Equivalent            => Axiom_Hash_Equivalent);
   package U_HMaps is new SPARK.Containers.Formal.Unbounded_Hashed_Maps
     (Key_Type        => T,
      Element_Type    => T,
      Equivalent_Keys => Equivalent,
      Hash            => Hash);
   package Ax_U_HMaps is new SPARK.Containers.Formal.Unbounded_Hashed_Maps
     (Key_Type                   => T,
      Element_Type               => T,
      Equivalent_Keys            => Equivalent,
      Hash                       => Hash,
      Eq_Reflexive               => Axiom_Eq_Reflexive,
      Eq_Symmetric               => Axiom_Eq_Symmetric,
      Eq_Transitive              => Axiom_Eq_Transitive,
      Equivalent_Keys_Reflexive  => Lemma_Equivalent_Reflexive,
      Equivalent_Keys_Symmetric  => Axiom_Equivalent_Symmetric,
      Equivalent_Keys_Transitive => Axiom_Equivalent_Transitive,
      Hash_Equivalent            => Axiom_Hash_Equivalent);
end Test_HMaps;
