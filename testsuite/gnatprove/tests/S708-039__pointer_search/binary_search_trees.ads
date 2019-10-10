pragma SPARK_Mode(On);

package Binary_Search_Trees is

   type Binary_Search_Tree is limited private;

   -- Reclaims the memory associated with the given binary search tree.
   -- This procedure leaves the tree in a properly initialized state so it can be reused.
   procedure Free(Tree : in out Binary_Search_Tree);

   -- Inserts the given item into the given tree.
   procedure Insert(Tree : in out Binary_Search_Tree; Item : in Integer)
     with Pre => Size(Tree) < Natural'Last;

   -- Returns True if the given item is in the given tree; False otherwise.
   function Lookup(Tree : Binary_Search_Tree; Item : Integer) return Boolean;

   -- Returns the smallest value in the given tree.
   function Minimum(Tree : Binary_Search_Tree) return Integer
     with Pre => Size(Tree) > 0;

   -- Returns the largest value in the given tree.
   --function Maximum(Tree : Binary_Search_Tree) return Integer
   --  with Pre => Size(Tree) > 0;

   -- Returns how many nodes are in the given tree.
   function Size(Tree : Binary_Search_Tree) return Natural;

private

   type Tree_Node;
   type Node_Access is access Tree_Node;

   type Tree_Node is
      record
         Data  : Integer;
         Left  : Node_Access;
         Right : Node_Access;
      end record;

   type Binary_Search_Tree is limited
      record
         Root : Node_Access := null;
         Size : Natural := 0;
      end record;

   function Size(Tree : Binary_Search_Tree) return Natural is
      (Tree.Size);

end Binary_Search_Trees;
