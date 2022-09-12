with SPARK.Containers.Formal.Vectors;
package FVectors is
   type Index is range 1 .. 100;
   package Vec is new SPARK.Containers.Formal.Vectors (Index, Integer);
end FVectors;
