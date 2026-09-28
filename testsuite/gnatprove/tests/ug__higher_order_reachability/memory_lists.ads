with SPARK.Containers.Functional.Infinite_Sequences;
with SPARK.Containers.Functional.Sets;
with SPARK.Higher_Order.Reachability;

package Memory_Lists is

   type Cell is record
      Value : Integer;
      Next  : Natural;
   end record;
   --  A cell of a list, the value 0 for Next marks the end of the list

   type Memory is array (Positive range <>) of Cell;

   function Next (C : Cell) return Natural is (C.Next);

   package Index_Sets is new SPARK.Containers.Functional.Sets (Positive);

   package Index_Sequences is new
     SPARK.Containers.Functional.Infinite_Sequences
       (Positive, Use_Logical_Equality => True);

   package Lists is new SPARK.Higher_Order.Reachability
     (Index_Type             => Positive,
      No_Index               => 0,
      Cell_Type              => Cell,
      Memory_Type            => Memory,
      Next                   => Next,
      Memory_Index_Sets      => Index_Sets,
      Memory_Index_Sequences => Index_Sequences);

end Memory_Lists;
