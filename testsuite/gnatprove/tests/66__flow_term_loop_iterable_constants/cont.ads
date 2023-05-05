with SPARK.Containers.Formal.Unbounded_Ordered_Sets;

package Cont with SPARK_Mode is
   package My_Sets is new SPARK.Containers.Formal.Unbounded_Ordered_Sets (Integer);
   use My_Sets;

   S : Set;

   procedure Include (I : Integer);
end Cont;
