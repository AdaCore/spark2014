with Ada.Containers.Formal_Vectors;

package My_Vectors with SPARK_Mode is
   subtype My_Index is Positive range 1 .. 10;
   package V is new Ada.Containers.Formal_Vectors
     (My_Index, Positive, Bounded => False);

   package S is new V.Generic_Sorting;

   procedure Test_Vectors;
end My_Vectors;
