pragma Extensions_Allowed (On);

with SPARK.Big_Integers; use SPARK.Big_Integers;
with SPARK.Pointers.Auto_Reclaimed.Immutable;
with SPARK.Pointers.Handles.Auto_Reclaimed_Handles;

--  A persistent binary tree over SPARK.Pointers.Auto_Reclaimed.Immutable.
--
--  The companion of 1448__pointers_persistent_list, and the case that list
--  does not cover. There the cell stores its own length, which gives Length
--  in O(1) and supplies the measure that makes the recursive definitions
--  terminate. Here nothing is stored: the measure comes from the library's
--  Multiway_Structural_Variant, which is sound because Next returns a part
--  of its input object and immutable structures cannot form a cycle.
--
--  What that buys, against storing a size in every node: no field in the
--  node, no structural invariant tying the stored size to the shape, and no
--  Runtime precondition bounding it in the client's own API.

procedure Persistent_Tree with SPARK_Mode is

   package Node_Handles is new
     SPARK.Pointers.Handles.Auto_Reclaimed_Handles.Without_Weak_Handles;

   type Way is (Left, Right);

   type Child_Array is array (Way) of aliased Node_Handles.Handle;

   type Tree_Node is record
      Value    : Integer;
      Children : Child_Array;
   end record;

   package Trees is new SPARK.Pointers.Auto_Reclaimed.Immutable (Tree_Node);
   use Trees;

   package Ops is new Trees.Handle_Operations (Node_Handles);
   use Ops;

   function Id (N : Tree_Node) return Tree_Node is (N) with Global => null;
   function New_Node is new Trees.Create (Tree_Node, Id);

   function Child_Of (O : not null access constant Tree_Node; W : Way)
     return access constant Node_Handles.Handle
   is (O.Children (W)'Access)
   with Global => null;

   package Variant is new Ops.Multiway_Structural_Variant (Way, Child_Of);

   --  The only structural invariant there is: every child handle is valid.
   --  Nothing relates a stored size to the shape, because nothing is stored.

   function Valid_Tree (T : Pointer) return Boolean
   is (T = Null_Pointer
       or else
         (for all W in Way =>
            Valid_Handle (Child_Of (Constant_Reference (T), W).all)
            and then Valid_Tree
                       (Of_Handle (Child_Of (Constant_Reference (T), W).all))))
   with
     Ghost              => Static,
     Global             => null,
     Subprogram_Variant => (Decreases => Variant.Weight (T));

   function Child (T : Pointer; W : Way) return Pointer
   is (Of_Handle (Child_Of (Constant_Reference (T), W).all))
   with
     Global => null,
     Pre    => (Runtime => T /= Null_Pointer, Static => Valid_Tree (T)),
     Post   => (Static => Valid_Tree (Child'Result));

   function Value_Of (T : Pointer) return Integer
   is (Constant_Reference (T).Value)
   with Global => null, Pre => T /= Null_Pointer;

   --  The number of nodes. Ghost, and derived rather than stored, so it can
   --  never disagree with the shape.

   function Size (T : Pointer) return Big_Natural
   is (if T = Null_Pointer
       then Big_Natural'(0)
       else 1 + Size (Child (T, Left)) + Size (Child (T, Right)))
   with
     Ghost              => Static,
     Global             => null,
     Pre                => Valid_Tree (T),
     Subprogram_Variant => (Decreases => Variant.Weight (T));

   --  A non-ghost traversal. The measure is a Static ghost function, so the
   --  variant names that level; the subprogram itself is ordinary code.

   function Member (T : Pointer; X : Integer) return Boolean
   is (T /= Null_Pointer
       and then (Value_Of (T) = X
                 or else Member (Child (T, Left), X)
                 or else Member (Child (T, Right), X)))
   with
     Global             => null,
     Pre                => (Static => Valid_Tree (T)),
     Subprogram_Variant => (Static => (Decreases => Variant.Weight (T)));

   --  Building. Node_Of shares the whole of L and R rather than copying.

   function Leaf (X : Integer) return Pointer
   is (New_Node
         ((Value    => X,
           Children => [others => Null_Handle])))
   with
     Global => null,
     Post   =>
       (Runtime => Leaf'Result /= Null_Pointer,
        Static  => Valid_Tree (Leaf'Result));

   function Node_Of (X : Integer; L, R : Pointer) return Pointer
   is (New_Node
         ((Value    => X,
           Children => [Left => To_Handle (L), Right => To_Handle (R)])))
   with
     Global => null,
     Pre    => (Static => Valid_Tree (L) and then Valid_Tree (R)),
     Post   =>
       (Runtime => Node_Of'Result /= Null_Pointer,
        Static  =>
          Valid_Tree (Node_Of'Result)
          and then Value_Of (Node_Of'Result) = X
          and then Logical_Eq (Child (Node_Of'Result, Left), L)
          and then Logical_Eq (Child (Node_Of'Result, Right), R));

   --  Two trees grown from the same subtree share every node of it, and the
   --  subtree is exactly as it was. There is no frame condition to state.

   procedure Demo_Sharing (S : Pointer)
   with
     Global => null,
     Pre    => (Runtime => S /= Null_Pointer, Static => Valid_Tree (S));

   procedure Demo_Sharing (S : Pointer) is
      T1 : constant Pointer := Node_Of (1, S, Null_Pointer);
      T2 : constant Pointer := Node_Of (2, Null_Pointer, S);
   begin
      pragma Assert (Static => Logical_Eq (Child (T1, Left), S));
      pragma Assert (Static => Logical_Eq (Child (T2, Right), S));
      pragma Assert (Static => Valid_Tree (S));
      pragma Assert (Static => Size (T1) = Size (S) + 1);
      pragma Assert (Static => Size (T2) = Size (S) + 1);
   end Demo_Sharing;

   S : constant Pointer := Node_Of (0, Leaf (1), Leaf (2));

begin
   pragma Assert (Static => Valid_Tree (S));
   pragma Assert (Static => Size (S) = 3);
   pragma Assert (Member (S, 1));
   pragma Assert (not Member (S, 7));
   Demo_Sharing (S);
end Persistent_Tree;
