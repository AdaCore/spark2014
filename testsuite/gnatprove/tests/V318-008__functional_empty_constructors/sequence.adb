with Ada.Assertions; use Ada.Assertions;
with SPARK.Containers.Functional.Vectors;
with Ada.Containers; use Ada.Containers;

procedure Sequence with SPARK_Mode is

   package Containers is new SPARK.Containers.Functional.Vectors
     (Index_Type => Positive,
      Element_Type => Natural);

   Seq : Containers.Sequence := Containers.Empty_Sequence;

begin
   --  To make sure that the Sequence is actually empty

   pragma Assert (Containers.Length (Seq) = 0);

end Sequence;
