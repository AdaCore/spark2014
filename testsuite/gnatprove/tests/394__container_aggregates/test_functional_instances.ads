with SPARK.Containers.Functional.Multisets;
with SPARK.Containers.Functional.Vectors;
with SPARK.Containers.Functional.Sets;
with SPARK.Containers.Functional.Maps;
with SPARK.Containers.Functional.Infinite_Sequences;
with SPARK.Big_Integers; use SPARK.Big_Integers;

package Test_Functional_Instances is

   subtype Index_Type is Positive;
   subtype Key_Type is Positive;
   subtype Element_Type is Positive;

   package Vectors is new SPARK.Containers.Functional.Vectors (Index_Type, Element_Type);
   package Sets is new SPARK.Containers.Functional.Sets (Element_Type);
   package Maps is new SPARK.Containers.Functional.Maps (Key_Type, Element_Type);
   package Seqs is new SPARK.Containers.Functional.Infinite_Sequences (Element_Type);
   package Multisets is new SPARK.Containers.Functional.Multisets (Element_Type);

end;
