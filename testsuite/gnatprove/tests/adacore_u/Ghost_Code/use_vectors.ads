with Ada.Containers.Functional_Vectors; use Ada.Containers;

package Use_Vectors
  with SPARK_Mode, Ghost
is
   subtype Resource is Natural range 0 .. 1000;
   subtype Index is Natural range 1 .. 42;

   package Seqs is new Ada.Containers.Functional_Vectors (Index, Resource);
   use Seqs;

   function Create return Sequence with
     Post => (for all K in 1 .. Last (Create'Result) =>
                Get (Create'Result, K) = K);

end Use_Vectors;
