with SPARK.Containers.Formal.Hashed_Sets;
with SPARK.Containers.Formal.Unbounded_Hashed_Sets;

with Types;  use Types;
with Axioms; use Axioms;

package Test_HSets with SPARK_Mode is
   package HSets is new SPARK.Containers.Formal.Hashed_Sets
     (Element_Type        => T,
      Equivalent_Elements => Equivalent,
      Hash                => Hash);
   package Ax_HSets is new SPARK.Containers.Formal.Hashed_Sets
     (Element_Type                   => T,
      Equivalent_Elements            => Equivalent,
      Hash                           => Hash,
      Eq_Reflexive                   => Axiom_Eq_Reflexive,
      Eq_Symmetric                   => Axiom_Eq_Symmetric,
      Eq_Transitive                  => Axiom_Eq_Transitive,
      Equivalent_Elements_Reflexive  => Axiom_Equivalent_Reflexive,
      Equivalent_Elements_Symmetric  => Axiom_Equivalent_Symmetric,
      Equivalent_Elements_Transitive => Axiom_Equivalent_Transitive,
      Hash_Equivalent                => Axiom_Hash_Equivalent);
   package Gen_Keys is new Ax_HSets.Generic_Keys
     (Key_Type        => T,
      Key             => F,
      Hash            => Hash,
      Equivalent_Keys => Equivalent);
   package Ax_Gen_Keys is new Ax_HSets.Generic_Keys
     (Key_Type        => T,
      Key             => F,
      Hash            => Hash,
      Equivalent_Keys => Equivalent,
      Eq_Compatible   => Axiom_Eq_Compatible,
      Hash_Compatible => Axiom_Hash_Compatible);
   package U_HSets is new SPARK.Containers.Formal.Unbounded_Hashed_Sets
     (Element_Type        => T,
      Equivalent_Elements => Equivalent,
      Hash                => Hash);
   package Ax_U_HSets is new SPARK.Containers.Formal.Unbounded_Hashed_Sets
     (Element_Type                   => T,
      Equivalent_Elements            => Equivalent,
      Hash                           => Hash,
      Eq_Reflexive                   => Axiom_Eq_Reflexive,
      Eq_Symmetric                   => Axiom_Eq_Symmetric,
      Eq_Transitive                  => Axiom_Eq_Transitive,
      Equivalent_Elements_Reflexive  => Axiom_Equivalent_Reflexive,
      Equivalent_Elements_Symmetric  => Axiom_Equivalent_Symmetric,
      Equivalent_Elements_Transitive => Axiom_Equivalent_Transitive,
      Hash_Equivalent                => Axiom_Hash_Equivalent);
   package U_Gen_Keys is new Ax_U_HSets.Generic_Keys
     (Key_Type        => T,
      Key             => F,
      Hash            => Hash,
      Equivalent_Keys => Equivalent);
   package Ax_U_Gen_Keys is new Ax_U_HSets.Generic_Keys
     (Key_Type        => T,
      Key             => F,
      Hash            => Hash,
      Equivalent_Keys => Equivalent,
      Eq_Compatible   => Axiom_Eq_Compatible,
      Hash_Compatible => Axiom_Hash_Compatible);
end Test_HSets;
