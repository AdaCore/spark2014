with Ada.Containers.Formal_Indefinite_Vectors;

package My_Vectors with SPARK_Mode is
   subtype My_Index is Positive range 1 .. 10;
   package V is new Ada.Containers.Formal_Indefinite_Vectors
     (My_Index, Positive, Bounded => False, Max_Size_In_Storage_Elements => Positive'Size);

   package S is new V.Generic_Sorting;

   procedure Test_Vectors;
end My_Vectors;
