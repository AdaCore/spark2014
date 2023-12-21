with SPARK.Containers.Functional.Multisets;
with SPARK.Containers.Functional.Vectors;
with SPARK.Containers.Functional.Sets;
with SPARK.Containers.Functional.Maps;
with SPARK.Containers.Functional.Infinite_Sequences;

package Test_Functional_Predicate_Instances is

   subtype Index_Type is Positive;
   subtype Key_Type is Positive;
   type Rec is record Value : Integer; end record;
   subtype Element_Type is Rec with Predicate => Element_Type.Value > 0;
   function R (Val : Integer) return Rec is (Rec'(Value => Val));

   package Vectors is new SPARK.Containers.Functional.Vectors (Index_Type, Element_Type);
   package Sets is new SPARK.Containers.Functional.Sets (Element_Type);
   package Maps is new SPARK.Containers.Functional.Maps (Key_Type, Element_Type);
   package Seqs is new SPARK.Containers.Functional.Infinite_Sequences (Element_Type);

   subtype Integer_Element_Type is Integer with Predicate => Integer_Element_Type > 0;
   package Multisets is new SPARK.Containers.Functional.Multisets (Integer_Element_Type);

end;
