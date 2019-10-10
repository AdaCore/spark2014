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

      procedure Insert_Node
        (Starting_At : not null Node_Access; Item : in Integer; Size : in out Natural)
        with
          Pre => Size < Natural'Last
      is
      begin
         if Item = Starting_At.Data then
            return;
         end if;

         if Item < Starting_At.Data then
            if Starting_At.Left = null then
               Starting_At.Left := new Tree_Node'(Data => Item, Left => null, Right => null);
               Size := Size + 1;
            else
               Insert_Node(Starting_At.Left, Item, Size);
            end if;

         else
            if Starting_At.Right = null then
               Starting_At.Right := new Tree_Node'(Data => Item, Left => null, Right => null);
               Size := Size + 1;
            else
               Insert_Node(Starting_At.Right, Item, Size);
            end if;

         end if;
      end Insert_Node;

   begin
      if Tree.Root = null then
         Tree.Root := new Tree_Node'(Data => Item, Left => null, Right => null);
         Tree.Size := Tree.Size + 1;
      else
         Insert_Node(Tree.Root, Item, Tree.Size);
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


   function Minimum_Node
     (Starting_At : not null access constant Tree_Node) return not null access constant Tree_Node
   is
      Current : not null access constant Tree_Node := Starting_At;

      -- The following version produces the message "compiler-generated raise statement is not
      -- yet supported" on the final return statement of this function. I assume this has some-
      -- thing to do with returning an "access constant Tree_Node" as a "not null access constant
      -- Tree_Node." Doesn't Ada normally raise Constraint_Error there when the return value is
      -- null? Why is this special?
      --
      -- Current : access constant Tree_Node := Starting_At;
   begin
      while Current.Left /= null loop
         Current := Current.Left;
      end loop;
      return Current;
   end Minimum_Node;


   function Minimum(Tree : Binary_Search_Tree) return Integer is
   begin
      return Minimum_Node(Tree.Root).Data;
   end Minimum;


end Binary_Search_Trees;
