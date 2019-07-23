with Ada.Containers.Formal_Vectors;
use Ada.Containers;

package Sum_Elem with
  SPARK_Mode
is

   N : constant := 6;
   type Index_Count is range 0 .. N;
   subtype Index is Index_Count range 0 .. Index_Count'Last - 1;

   type Interval is record
      First : Index;
      Last  : Index;
   end record;
   type Partition_Index is range 0 .. 10_000;
   package Partitions is new
     Formal_Vectors (Index_Type   => Partition_Index,
                     Element_Type => Interval);
   subtype Partition is Partitions.Vector;
   use Partitions;

   procedure Local (P : Partition; X : Partition_Index) with
     Pre => X in 0 .. Partition_Index (Length (P)) - 1 and then
            (for all J in First_Index (P) .. Last_Index (P) => Element (P, J).First + Element (P, J).Last in Index);

   P : Partition (10);

   procedure Main;

end Sum_Elem;
