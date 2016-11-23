with Ada.Containers.Formal_Vectors;

package P is
   package My_Vectors is new
     Ada.Containers.Formal_Vectors (Index_Type   => Positive,
                                    Element_Type => Integer,
                                    "="          => "=");

   use type Ada.Containers.Count_Type;

   procedure Dummy (D : Ada.Containers.Count_Type);
end P;
