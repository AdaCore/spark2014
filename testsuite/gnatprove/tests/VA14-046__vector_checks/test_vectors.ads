with SPARK.Containers.Formal.Vectors;
with SPARK.Containers.Formal.Unbounded_Vectors;

with Types;  use Types;
with Axioms; use Axioms;

package Test_Vectors with SPARK_Mode is
   package Vectors is new SPARK.Containers.Formal.Vectors
     (Index_Type   => Positive,
      Element_Type => T);
   package Ax_Vectors is new SPARK.Containers.Formal.Vectors
     (Index_Type    => Positive,
      Element_Type  => T,
      Eq_Reflexive  => Axiom_Eq_Reflexive,
      Eq_Symmetric  => Axiom_Eq_Symmetric,
      Eq_Transitive => Axiom_Eq_Transitive);
   package Sorting is new Ax_Vectors.Generic_Sorting;
   package Ax_Sorting is new Ax_Vectors.Generic_Sorting
     (Lt_Irreflexive => Axiom_Lt_Irreflexive,
      Lt_Asymmetric  => Axiom_Lt_Asymmetric,
      Lt_Transitive  => Axiom_Lt_Transitive,
      Lt_Order       => Axiom_Lt_Order);
   package U_Vectors is new SPARK.Containers.Formal.Vectors
     (Index_Type   => Positive,
      Element_Type => T);
   package Ax_U_Vectors is new SPARK.Containers.Formal.Vectors
     (Index_Type    => Positive,
      Element_Type  => T,
      Eq_Reflexive  => Axiom_Eq_Reflexive,
      Eq_Symmetric  => Axiom_Eq_Symmetric,
      Eq_Transitive => Axiom_Eq_Transitive);
   package U_Sorting is new Ax_U_Vectors.Generic_Sorting;
   package Ax_U_Sorting is new Ax_U_Vectors.Generic_Sorting
     (Lt_Irreflexive => Axiom_Lt_Irreflexive,
      Lt_Asymmetric  => Axiom_Lt_Asymmetric,
      Lt_Transitive  => Axiom_Lt_Transitive,
      Lt_Order       => Axiom_Lt_Order);
end Test_Vectors;
