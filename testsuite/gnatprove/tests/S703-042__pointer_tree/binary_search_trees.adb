pragma SPARK_Mode(On);

with Ada.Unchecked_Deallocation;

package body Binary_Search_Trees is

   procedure Free_Tree_Node is
     new Ada.Unchecked_Deallocation(Object => Tree_Node, Name => Node_Access);

   procedure Free(Tree : in out Binary_Search_Tree) is

      procedure Free_Node(Starting_At : in out Node_Access) is
      begin
         if Starting_At /= null then
            Free_Node(Starting_At.Left);
            Free_Node(Starting_At.Right);
            Free_Tree_Node(Starting_At);
         end if;
      end Free_Node;

   begin
      Free_Node(Starting_At => Tree.Root);
      Tree.Size := 0;
   end Free;


   procedure Insert(Tree : in out Binary_Search_Tree; Item : in Integer) is

      Node : Node_Access;

      procedure Insert_Node(Starting_At : not null Node_Access)
        with
          Global => (In_Out => (Tree, Node)),
          Pre => Size(Tree) < Natural'Last and Node /= null
      is
      begin
         if Node.Data = Starting_At.Data then
            return;
         end if;

         if Node.Data < Starting_At.Data then
            if Starting_At.Left = null then
               Starting_At.Left := Node;
               -- Node := null;
               Tree.Size := Tree.Size + 1;
            else
               Insert_Node(Starting_At.Left);
            end if;

         else
            if Starting_At.Right = null then
               Starting_At.Right := Node;
               -- Node := null;
               Tree.Size := Tree.Size + 1;
            else
               Insert_Node(Starting_At.Right);
            end if;

         end if;
      end Insert_Node;

   begin
      Node := new Tree_Node'(Data => Item, Left => null, Right => null);
      if Tree.Root = null then
         Tree.Root := Node;
         Tree.Size := Tree.Size + 1;
      else
         Insert_Node(Tree.Root);
      end if;
   end Insert;


   function Lookup(Tree : Binary_Search_Tree; Item : Integer) return Boolean is

      function Lookup_Node(Starting_At : Node_Access) return Boolean is
         Result : Boolean;
      begin
         if Starting_At = null then
            Result := False;
         else
            if Item = Starting_At.Data then
               Result := True;
            elsif Item < Starting_At.Data then
               Result := Lookup_Node(Starting_At.Left);
            else
               Result := Lookup_node(Starting_At.Right);
            end if;
         end if;
         return Result;
      end Lookup_Node;

   begin
      return Lookup_Node(Starting_At => Tree.Root);
   end Lookup;


end Binary_Search_Trees;
