with SPARK.Containers.Formal.Vectors;

package Cont with SPARK_Mode is
   N : constant := 1024;
   type T is range 0 .. N;
   subtype S  is T range 1 .. T'Last;
   package P is new
     SPARK.Containers.Formal.Vectors
       (Index_Type => S,
        Element_Type => Integer);
end Cont;
