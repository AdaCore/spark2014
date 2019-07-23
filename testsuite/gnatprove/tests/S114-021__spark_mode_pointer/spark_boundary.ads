with Ada.Containers.Functional_Vectors;
package SPARK_Boundary with SPARK_Mode is
   package Model is new Ada.Containers.Functional_Vectors (Positive, Integer);
end SPARK_Boundary;
