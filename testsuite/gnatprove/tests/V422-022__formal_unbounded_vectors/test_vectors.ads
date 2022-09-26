with SPARK.Containers.Formal.Unbounded_Vectors;

package Test_Vectors with SPARK_Mode is
   package V is new SPARK.Containers.Formal.Unbounded_Vectors (Positive, Natural);

   package S is new V.Generic_Sorting;

   procedure Run;

   procedure Large_Run;

   procedure Index_Negative;

end Test_Vectors;
