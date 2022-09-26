with Aida.Containers.Formal_Vectors;

pragma Elaborate_All (Aida.Containers.Formal_Vectors);

package Hnco.Test2 is
   pragma SPARK_Mode;

   package V_Type_Owner is new Aida.Containers.Formal_Vectors (Index_Type => Positive,
                                                               Element_Type => Integer);

   V : V_Type_Owner.Vector_Type;

   procedure Add_Elements_To_Vector;

end Hnco.Test2;
