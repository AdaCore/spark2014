with SPARK.Containers.Formal.Indefinite_Vectors;
package Vecs with SPARK_Mode is
   type Index_T is range 0 .. 1000;

   package Vec is new SPARK.Containers.Formal.Indefinite_Vectors
     (Index_Type   => Index_T,
      Element_Type => Integer,
      Bounded      => True);

end Vecs;
