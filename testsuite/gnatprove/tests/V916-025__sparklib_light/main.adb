with SPARK.Containers.Functional.Infinite_Sequences;
with SPARK.Containers.Functional.Maps;
with SPARK.Containers.Functional.Multisets;
with SPARK.Containers.Functional.Sets;
with SPARK.Containers.Functional.Vectors;
with SPARK.Containers.Functional.Infinite_Sequences.Higher_Order;
with SPARK.Containers.Functional.Maps.Higher_Order;
with SPARK.Containers.Functional.Sets.Higher_Order;
with SPARK.Containers.Functional.Vectors.Higher_Order;
with SPARK.Lemmas.Float_Arithmetic;

with SPARK.Containers.Formal.Doubly_Linked_Lists;

procedure Main with SPARK_Mode is

   --  Check that it is possible to instantiate functional containers

   package Seqs is new
     SPARK.Containers.Functional.Infinite_Sequences (Integer);
   package Seqs_HO is new Seqs.Higher_Order;
   package Maps is new SPARK.Containers.Functional.Maps (Integer, Integer);
   package Maps_HO is new Maps.Higher_Order;
   package Multisets is new SPARK.Containers.Functional.Multisets (Integer);
   package Sets is new SPARK.Containers.Functional.Sets (Integer);
   package Sets_HO is new Sets.Higher_Order;
   package Vecs is new SPARK.Containers.Functional.Vectors (Positive, Integer);
   package Vecs_HO is new Vecs.Higher_Order;

   --  Check that it is possible to instantiate formal containers

   package Lists is new SPARK.Containers.Formal.Doubly_Linked_Lists (Integer);
begin
   null;
end Main;
