with SPARK.Containers.Formal.Ordered_Sets;
with SPARK.Containers.Formal.Unbounded_Ordered_Sets;

with Types;  use Types;
with Axioms; use Axioms;

package Test_OSets with SPARK_Mode is
   package OSets is new SPARK.Containers.Formal.Ordered_Sets
     (Element_Type => T);
   package Ax_OSets is new SPARK.Containers.Formal.Ordered_Sets
     (Element_Type   => T,
      Eq_Reflexive   => Axiom_Eq_Reflexive,
      Eq_Symmetric   => Axiom_Eq_Symmetric,
      Eq_Transitive  => Axiom_Eq_Transitive,
      Lt_Irreflexive => Axiom_Lt_Irreflexive,
      Lt_Asymmetric  => Axiom_Lt_Asymmetric,
      Lt_Transitive  => Axiom_Lt_Transitive,
      Lt_Order       => Axiom_Lt_Order);
   package Gen_Keys is new Ax_OSets.Generic_Keys
     (Key_Type => T,
      Key      => F);
   package Ax_Gen_Keys is new Ax_OSets.Generic_Keys
     (Key_Type      => T,
      Key           => F,
      Lt_Compatible => Axiom_Lt_Compatible);
   package U_OSets is new SPARK.Containers.Formal.Unbounded_Ordered_Sets
     (Element_Type => T);
   package Ax_U_OSets is new SPARK.Containers.Formal.Unbounded_Ordered_Sets
     (Element_Type   => T,
      Eq_Reflexive   => Axiom_Eq_Reflexive,
      Eq_Symmetric   => Axiom_Eq_Symmetric,
      Eq_Transitive  => Axiom_Eq_Transitive,
      Lt_Irreflexive => Axiom_Lt_Irreflexive,
      Lt_Asymmetric  => Axiom_Lt_Asymmetric,
      Lt_Transitive  => Axiom_Lt_Transitive,
      Lt_Order       => Axiom_Lt_Order);
   package U_Gen_Keys is new Ax_U_OSets.Generic_Keys
     (Key_Type => T,
      Key      => F);
   package Ax_U_Gen_Keys is new Ax_U_OSets.Generic_Keys
     (Key_Type      => T,
      Key           => F,
      Lt_Compatible => Axiom_Lt_Compatible);
end Test_Osets;
