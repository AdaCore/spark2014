with Ada.Containers.Formal_Vectors;
use Ada.Containers;

procedure Sum_Elem with
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
   function Eq_Interval (Left, Right : Interval) return Boolean is (Left = Right);
   package Partitions is new
     Formal_Vectors (Index_Type   => Partition_Index,
                     Element_Type => Interval,
                     "="          => Eq_Interval);
   subtype Partition is Partitions.Vector;
   use Partitions;

   procedure Local (P : Partition; X : Partition_Index) with
     Pre => X in 0 .. Partition_Index (Length (P)) - 1 and then
            (for all J in First_Index (P) .. Last_Index (P) => Element (P, J).First + Element (P, J).Last in Index)
   is
   begin
      pragma Assert (Element (P, X).First + Element (P, X).Last in Index);
   end Local;

   P : Partition (10);

begin
   Append (P, Interval'(First => 1, Last => 1));
   Local (P, 0);
end Sum_Elem;
