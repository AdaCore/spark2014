with Ada.Containers.Formal_Ordered_Maps;
with Ada.Containers.Formal_Vectors;
with Ada.Containers.Formal_Doubly_Linked_Lists;
use Ada.Containers;

package Partition_Refinement with
  SPARK_Mode
is

   N : constant := 6;
   type Index_Count is range 0 .. N;
   subtype Index is Index_Count range 0 .. Index_Count'Last - 1;
   type Set is array (Index) of Positive;


   package Partitioning_Sets is new
     Formal_Doubly_Linked_Lists (Element_Type => Positive);

   subtype Partitioning_Set is Partitioning_Sets.List;
   use Partitioning_Sets;

   package Inverse_Sets is new
     Formal_Ordered_Maps (Key_Type     => Positive,
                          ELement_Type => Index);
   subtype Inverse_Set is Inverse_Sets.Map;
   use Inverse_Sets;

   type Interval is record
      First : Index;
      Last  : Index;
      Count : Index_Count;
   end record;
   type Partition_Index is range 0 .. 10_000;
   package Partitions is new
     Formal_Vectors (Index_Type   => Partition_Index,
                     Element_Type => Interval);
   subtype Partition is Partitions.Vector;
   use Partitions;

   type Inverse_Partition is array (Index) of Partition_Index;

   procedure Refine
     (A : in out Set;
      D : in out Inverse_Set;
      P : in out Partition;
      F : in out Inverse_Partition;
      X : in     Partitioning_Set)
   with
      Pre  => --  P is at most half full, to make space for the refinement
              2 * Length (P) <= Capacity (P) and then
              Length (P) <= Count_Type(Partition_Index'Last / 2) and then
              --  D is the inverse map of A
              (for all J in Index => Contains (D, A(J))) and then
              (for all C in D => A (Element (D, C)) = Key (D, C)) and then
              --  X is a subset of A
              (for all C in X => Contains (D, Element (X, C))) and then
              --  F maps indexes to their partition
              (for all J in Index => F(J) in 0 .. Partition_Index'Base (Length (P)) - 1) and then
              (for all J in Index => J in Element (P, F(J)).First .. Element (P, F(J)).Last) and then
              (for all J in 0 .. Partition_Index'Base (Length (P)) - 1 => (for all K in Index range Element (P, J).First .. Element (P, J).Last => F(K) = J)) and then
              --  component Count is initialized to zero
              (for all J in 0 .. Partition_Index(Length (P)) - 1 => Element (P, J).Count = 0),
      Post => --  F still maps indexes to their partition
              (for all J in Index => F(J) in 0 .. Partition_Index'Base (Length (P)) - 1) and then
              (for all J in Index => J in Element (P, F(J)).First .. Element (P, F(J)).Last);

end Partition_Refinement;
