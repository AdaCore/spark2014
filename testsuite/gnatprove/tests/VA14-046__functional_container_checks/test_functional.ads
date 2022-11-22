with SPARK.Containers.Functional.Infinite_Sequences;
with SPARK.Containers.Functional.Maps;
with SPARK.Containers.Functional.Sets;
with SPARK.Containers.Functional.Vectors;

with Types;  use Types;
with Axioms; use Axioms;

package Test_Functional with SPARK_Mode is
   package Sequences is new SPARK.Containers.Functional.Infinite_Sequences
     (Element_Type        => T,
      Equivalent_Elements => Equivalent);
   package Maps is new SPARK.Containers.Functional.Maps
     (Key_Type            => T,
      Element_Type        => T,
      Equivalent_Keys     => Equivalent,
      Equivalent_Elements => Equivalent);
   package Sets is new SPARK.Containers.Functional.Sets
     (Element_Type        => T,
      Equivalent_Elements => Equivalent);
   package Vectors is new SPARK.Containers.Functional.Vectors
     (Index_Type          => Positive,
      Element_Type        => T,
      Equivalent_Elements => Equivalent);
   package Ax_Sequences is new SPARK.Containers.Functional.Infinite_Sequences
     (Element_Type                   => T,
      Equivalent_Elements            => Equivalent,
      Eq_Reflexive                   => Axiom_Eq_Reflexive,
      Eq_Symmetric                   => Axiom_Eq_Symmetric,
      Eq_Transitive                  => Axiom_Eq_Transitive,
      Equivalent_Elements_Reflexive  => Axiom_Equivalent_Reflexive,
      Equivalent_Elements_Symmetric  => Axiom_Equivalent_Symmetric,
      Equivalent_Elements_Transitive => Axiom_Equivalent_Transitive);
   package Ax_Maps is new SPARK.Containers.Functional.Maps
     (Key_Type                       => T,
      Element_Type                   => T,
      Equivalent_Keys                => Equivalent,
      Equivalent_Elements            => Equivalent,
      Equivalent_Keys_Reflexive      => Lemma_Equivalent_Reflexive,
      Equivalent_Keys_Symmetric      => Axiom_Equivalent_Symmetric,
      Equivalent_Keys_Transitive     => Axiom_Equivalent_Transitive,
      Eq_Reflexive                   => Axiom_Eq_Reflexive,
      Eq_Symmetric                   => Axiom_Eq_Symmetric,
      Eq_Transitive                  => Axiom_Eq_Transitive,
      Equivalent_Elements_Reflexive  => Axiom_Equivalent_Reflexive,
      Equivalent_Elements_Symmetric  => Axiom_Equivalent_Symmetric,
      Equivalent_Elements_Transitive => Axiom_Equivalent_Transitive);
   package Ax_Sets is new SPARK.Containers.Functional.Sets
     (Element_Type                   => T,
      Equivalent_Elements            => Equivalent,
      Equivalent_Elements_Reflexive  => Lemma_Equivalent_Reflexive,
      Equivalent_Elements_Symmetric  => Axiom_Equivalent_Symmetric,
      Equivalent_Elements_Transitive => Axiom_Equivalent_Transitive);
   package Ax_Vectors is new SPARK.Containers.Functional.Vectors
     (Index_Type                     => Positive,
      Element_Type                   => T,
      Equivalent_Elements            => Equivalent,
      Eq_Reflexive                   => Axiom_Eq_Reflexive,
      Eq_Symmetric                   => Axiom_Eq_Symmetric,
      Eq_Transitive                  => Axiom_Eq_Transitive,
      Equivalent_Elements_Reflexive  => Axiom_Equivalent_Reflexive,
      Equivalent_Elements_Symmetric  => Axiom_Equivalent_Symmetric,
      Equivalent_Elements_Transitive => Axiom_Equivalent_Transitive);
end Test_Functional;
