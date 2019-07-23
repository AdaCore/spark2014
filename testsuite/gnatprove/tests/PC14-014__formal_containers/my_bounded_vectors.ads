with Ada.Containers.Formal_Vectors;

package My_Bounded_Vectors with SPARK_Mode is
   package V is new Ada.Containers.Formal_Vectors
     (Positive, Positive);

   package S is new V.Generic_Sorting;

   procedure Test_Bounded_Vectors;
end My_Bounded_Vectors;
