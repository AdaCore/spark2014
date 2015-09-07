package Interval_Tree
  with
    SPARK_Mode     => On,
    Abstract_State => Internal_Tree,
    Initializes    => Internal_Tree
is
   type Interval is
      record
         Low  : Float;
         High : Float;
      end record;

   -- Inserts Item into the tree.
   procedure Insert (Item : in Interval)
     with
       Global  => (In_Out => Internal_Tree),
       Depends => (Internal_Tree => (Internal_Tree, Item)),
       Post    => Size = Size'Old + 1;

   function Size return Natural
     with
       Global => (Input => Internal_Tree);

   -- Destroys the tree. After this call the tree can be reused.
   procedure Destroy
     with
       Global => (In_Out => Internal_Tree),
       Post   => Size = 0;

end Interval_Tree;
