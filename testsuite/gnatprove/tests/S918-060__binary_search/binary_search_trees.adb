pragma SPARK_Mode(On);

with Ada.Unchecked_Deallocation;

package body Binary_Search_Trees is

   procedure Free_Tree_Node is
     new Ada.Unchecked_Deallocation(Object => Tree_Node, Name => Node_Access);

   procedure Free(Tree : in out Binary_Search_Tree) is

      procedure Free_Node(Starting_At : in out Node_Access)
        with Post => Starting_At = null
      is
      begin
         if Starting_At /= null then
            Free_Node(Starting_At.Left);
            Free_Node(Starting_At.Right);
            Free_Tree_Node(Starting_At);
         end if;
      end Free_Node;

      Temp : Node_Access := Tree.Root;
   begin
      Free_Node(Starting_At => Temp);
      Tree := (Root => Temp, Size => 0);
   end Free;


   procedure Insert(Tree : in out Binary_Search_Tree; Item : in Integer) is

      procedure Insert_Node
        (Starting_At : not null Node_Access; Item : in Integer; Size : in out Natural)
        with
          Pre  => Size < Natural'Last,
          Post => (Size = Size'Old) or (Size = Size'Old + 1)
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

      New_Node : Node_Access;
   begin
      if Tree.Root = null then
         New_Node := new Tree_Node'(Data => Item, Left => null, Right => null);
         Tree := (Root => New_Node, Size => Tree.Size + 1);
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
