with Ada.Unchecked_Deallocation;

package body Interval_Trees
  with SPARK_Mode => Off is

   procedure Deallocate_Node is new
      Ada.Unchecked_Deallocation (Object => Tree_Node, Name => Tree_Node_Access);

   -- Inserts Item into tree T. Duplicate items overwrite existing tree elements.
   procedure Insert (T : in out Tree; Item : in Interval) is
      New_Node : Tree_Node_Access := new Tree_Node'(Data => Item, Maximum => Item.High, others => <>);

      procedure Subtree_Insert (Pointer : in not null Tree_Node_Access) is
      begin
         if Item.Low <= Pointer.Data.Low then
            if Pointer.Left_Child = null then
               Pointer.Left_Child := New_Node;
               New_Node.Parent := Pointer;
            else
               Subtree_Insert (Pointer.Left_Child);
               Pointer.Maximum := Float'Max (Pointer.Maximum, Pointer.Left_Child.Maximum);
            end if;
         else
            if Pointer.Right_Child = null then
               Pointer.Right_Child := New_Node;
               New_Node.Parent := Pointer;
            else
               Subtree_Insert (Pointer.Right_Child);
               Pointer.Maximum := Float'Max (Pointer.Maximum, Pointer.Right_Child.Maximum);
            end if;
         end if;
      end Subtree_Insert;

   begin
      if T.Root = null then
         T.Root := New_Node;
      else
         Subtree_Insert (T.Root);
      end if;
      T.Count := T.Count + 1;
   end Insert;


   function Size (T : in Tree) return Natural is
   begin
      return T.Count;
   end Size;


   procedure Finalize (T : in out Tree) is

      procedure Deallocate_Subtree (Pointer : in out Tree_Node_Access) is
      begin
         if Pointer = null then return; end if;
         Deallocate_Subtree (Pointer.Left_Child);
         Deallocate_Subtree (Pointer.Right_Child);
         Deallocate_Node (Pointer);
      end Deallocate_Subtree;

   begin
      Deallocate_Subtree (T.Root);
      T.Count := 0;
   end Finalize;

end Interval_Trees;
