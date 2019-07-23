with Ada.Containers.Functional_Vectors;
with Ada.Containers.Functional_Sets;
use Ada.Containers;

package Tree_Model with SPARK_Mode is

   Max : constant := 100;
   --  Maximum number of nodes in a tree

   Empty : constant := 0;

   subtype Index_Type is Count_Type range 1 .. Max;
   --  Numbering for tree nodes

   subtype Extended_Index_Type is Index_Type'Base range Empty .. Max;
   --  Numbering extended with the value Empty representing the absence of node

   type Position_Type is (Left, Right, Top);
   subtype Direction is Position_Type range Left .. Right;

   subtype Positive_Count_Type is Count_Type range 1 .. Count_Type'Last;
   package D_Seq is new Ada.Containers.Functional_Vectors
     (Positive_Count_Type, Direction);
   use D_Seq;
   --  Sequence of directions modelling a path from the root of the tree to a
   --  node in the tree.

   type Path_Type is record
      A : Sequence;
      K : Boolean := False;
   end record
   with Predicate => Length (A) < Max;
   --  Type used to model the path from the root of a tree to a given node,
   --  which may or not be in the tree:
   --    - if a node is in the tree, the corresponding path will have K = True,
   --      and A will denote the path from the root to this node.
   --    - if a node is not in the tree, the corresponding path will have
   --      K = False and A will be empty.

end Tree_Model;
