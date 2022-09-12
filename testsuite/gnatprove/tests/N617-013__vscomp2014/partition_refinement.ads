with SPARK.Containers.Formal.Ordered_Maps;
with SPARK.Containers.Formal.Vectors;
with SPARK.Containers.Formal.Doubly_Linked_Lists;
with Ada.Containers; use Ada.Containers;

package Partition_Refinement with
  SPARK_Mode
is

   N : constant := 6;
   type Index_Count is range 0 .. N;
   subtype Index is Index_Count range 0 .. Index_Count'Last - 1;

   type Interval is record
      First : Index;
      Last  : Index;
      Count : Index_Count;
   end record;
   type Partition_Index is range 0 .. 10_000;
   package Partitions is new
     SPARK.Containers.Formal.Vectors (Index_Type   => Partition_Index,
                                      Element_Type => Interval);
   subtype Partition is Partitions.Vector;
   use Partitions;

   type Inverse_Partition is array (Index) of Partition_Index;

   procedure Make_New_Partitions
     (P : in out Partition;
      F : in out Inverse_Partition);

end Partition_Refinement;
