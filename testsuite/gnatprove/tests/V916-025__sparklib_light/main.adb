with SPARK.Containers.Functional.Infinite_Sequences;
with SPARK.Containers.Functional.Maps;
with SPARK.Containers.Functional.Sets;
with SPARK.Containers.Functional.Vectors;

with SPARK.Containers.Formal.Doubly_Linked_Lists;

procedure Main with SPARK_Mode is

   --  Check that it is possible to instantiate functional containers

   package Seqs is new
     SPARK.Containers.Functional.Infinite_Sequences (Integer);
   package Maps is new SPARK.Containers.Functional.Maps (Integer, Integer);
   package Sets is new SPARK.Containers.Functional.Sets (Integer);
   package Vecs is new SPARK.Containers.Functional.Vectors (Positive, Integer);

   --  Check that it is possible to instantiate formal containers

   package Lists is new SPARK.Containers.Formal.Doubly_Linked_Lists (Integer);
begin
   null;
end Main;
