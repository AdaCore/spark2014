with Tree_Model; use Tree_Model;
use Tree_Model.D_Seq;
with Ada.Containers; use Ada.Containers;

--  This packages provides a SPARK implementation of binary trees. Since SPARK
--  forbids the use of pointers, trees are modeled using indexes inside an
--  array. The array is not global, as it would require referring to a global
--  structure in the tree type invariant which is not allowed in SPARK. To avoid
--  multiple copies, related trees are stored together forming a forest.

package Binary_Trees with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   type Forest is private with Default_Initial_Condition => Size (Forest) = 0;
   --  Containsory region shaped as a set of related binary trees

   function Size (F : Forest) return Extended_Index_Type;
   --  Number of allocated nodes in the forest

private

   type Cell is record
      Left, Right, Parent : Extended_Index_Type := Empty;
      Position            : Position_Type := Top;
   end record;
   type Cell_Array is array (Index_Type) of Cell;

   type Forest is record
      S : Extended_Index_Type := Empty;
      C : Cell_Array;
   end record
     with Type_Invariant => Tree_Structure (Forest);
   --  Component S gives the size of the forest. Only the cells up to index S
   --  belong to the forest. Cells after index S are free.

   function Tree_Structure (F : Forest) return Boolean with
     Global => null;
   --  Invariant of the structure of the forest

end Binary_Trees;
