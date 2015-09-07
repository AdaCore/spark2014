with Ada.Unchecked_Deallocation;
package body Interval_Tree
   with
      SPARK_Mode => Off
is
   type Tree_Node;
   type Tree_Node_Access is access Tree_Node;
   type Tree_Node is
      record
         Data        : Interval;
         Maximum     : Float;
         Parent      : Tree_Node_Access := null;
         Left_Child  : Tree_Node_Access := null;
         Right_Child : Tree_Node_Access := null;
      end record;

   -- Intantiate a procedure for deallocating node memory
   procedure Deallocate_Node is new Ada.Unchecked_Deallocation
                                       (Object => Tree_Node,
                                        Name   => Tree_Node_Access);
   type Tree is
      record
         Root  : Tree_Node_Access := null;
         Count : Natural := 0;
      end record;

   T : Tree;  -- The actual tree in this variable package

   procedure Insert (Item : in Interval) is
      New_Node : Tree_Node_Access; -- local to Insert, global to Subtree_Insert

      procedure Subtree_Insert (Pointer : in not null Tree_Node_Access) is
      begin
         if Item.Low <= Pointer.Data.Low then
            if Pointer.Left_Child = null then
               Pointer.Left_Child := New_Node;
               New_Node.Parent := Pointer;
            else
               Subtree_Insert (Pointer.Left_Child);
               Pointer.Maximum :=
                 Float'Max (Pointer.Maximum, Pointer.Left_Child.Maximum);
            end if;
         else
            if Pointer.Right_Child = null then
               Pointer.Right_Child := New_Node;
               New_Node.Parent := Pointer;
            else
               Subtree_Insert (Pointer.Right_Child);
               Pointer.Maximum :=
                 Float'Max (Pointer.Maximum, Pointer.Right_Child.Maximum);
            end if;
         end if;
      end Subtree_Insert;

   begin
      New_Node := new Tree_Node'(Data    => Item,
                                 Maximum => Item.High,
                                 others  => <>);
      if T.Root = null then
         T.Root := New_Node;
      else
         Subtree_Insert (T.Root);
      end if;
      T.Count := T.Count + 1;
   end Insert;


   function Size return Natural is
   begin
      return T.Count;
   end Size;

   procedure Destroy is

      procedure Deallocate_Subtree (Pointer : in out Tree_Node_Access) is
      begin
         if Pointer /= null then
            Deallocate_Subtree (Pointer.Left_Child);
            Deallocate_Subtree (Pointer.Right_Child);
            Deallocate_Node (Pointer);
         end if;
      end Deallocate_Subtree;

   begin
      Deallocate_Subtree (T.Root);
      T.Count := 0;
   end Destroy;

end Interval_Tree;
