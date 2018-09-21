with Ada.Containers.Formal_Indefinite_Vectors;
package Vecs with SPARK_Mode is
   type Index_T is range 0 .. 1000;

   package Vec is new Ada.Containers.Formal_Indefinite_Vectors
     (Index_Type   => Index_T,
      Element_Type => Integer,
      Bounded      => True);

end Vecs;
