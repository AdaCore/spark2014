with SPARK.Containers.Formal.Vectors;

package My_Bounded_Vectors with SPARK_Mode is
   package V is new SPARK.Containers.Formal.Vectors
     (Positive, Positive);

   package S is new V.Generic_Sorting;

   procedure Test_Bounded_Vectors;
end My_Bounded_Vectors;
