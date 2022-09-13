with SPARK.Containers.Formal.Unbounded_Vectors;
package Vecs with SPARK_Mode is
   type Index_T is range 0 .. 1000;

   package Vec is new SPARK.Containers.Formal.Unbounded_Vectors
     (Index_Type   => Index_T,
      Element_Type => Integer);

end Vecs;
